"""
Basic dialect interpreter.

Note: the basic dialect is woefully incomplete and the commands that
are provided are often not even compatible with their originals on the C64,
but they do try to support *some* of the BASIC 2.0 structure.

The most important thing that is missing is the ability to
to do any 'blocking' operation such as INPUT or WAIT.
(GET - to grab a single pressed key - is supported).
The SLEEP command is added more or less as a hack, to be able to at least
slow down the thing at certain points.

Written by Irmen de Jong (irmen@razorvine.net)
License: MIT open-source.
"""

import os
import math
import hashlib
import base64
import binascii
import sys
import platform
import random
import traceback
import re
import time
import numbers
from .shared import StdoutWrapper, do_load, do_dos, do_sys, FlowcontrolException


class BasicError(Exception):
    pass

class GotoCmdException(FlowcontrolException):
    def __init__(self, cmd_idx):
        self.cmd_idx = cmd_idx

class TimeValProxy:
    def __init__(self, memory, hz):
        self.memory = memory
        self.hz = hz

    def __str__(self):
        secs = ((self.memory[160] << 16) + (self.memory[161] << 8) + self.memory[162]) / self.hz
        h, secs = divmod(secs, 3600)
        m, secs = divmod(secs, 60)
        return "{:02d}{:02d}{:02d}".format(int(h), int(m), int(secs))

    def __repr__(self):
        return self.__str__()

    def __int__(self):
        jiffies = (self.memory[160] << 16) + (self.memory[161] << 8) + self.memory[162]
        return jiffies


class BasicInterpreter:
    F1_list_command = "list:"
    F3_run_command = "run:"
    F5_load_command = "load "
    F6_load_command = "load \"*\",8: "
    F7_dir_command = "\fdos\"$"

    def __init__(self, screen):
        self.screen = screen
        self.interactive = None   # will be set later, externally
        self.program = {}
        self.in_init = True
        self.next_cmd_run_idx = None
        self.sleep_until = None
        self.symbols = None
        self.program_lines = None
        self.cmd_lines = None
        self.program_line_idx_to_cmd_idx = None
        self.next_cmd_run_idx = None
        self.cmd_lines_to_program_line_idx = None
        self.forloops = {}
        self.data_line = None
        self.data_index = None
        self.sleep_until = None
        self.must_run_stop = False
        self.reset()
        self.in_init = False

    def start(self):
        pass

    def stop(self):
        pass

    def reset(self):
        self.symbols = {
            "platform": platform,
            "π": math.pi,
            "ti": TimeValProxy(self.screen.memory, self.screen.hz),
            "time": TimeValProxy(self.screen.memory, self.screen.hz),
        }
        for x in dir(math):
            if '_' not in x:
                self.symbols[x] = getattr(math, x)

        # example program to show each relation of the internal memory structure
        #    10 PRINT "START"
        #    20 FOR I=1 TO 5: ? I: NEXT I
        #    30 GOTO 20
        #
        # program -> dict {<basic line number>: <program line text>}
        #    e.g. {10: 'PRINT "START"', 20: 'FOR I=1 TO 5: ? I: NEXT I', 30: 'GOTO 20'}
        # program_lines -> array: each program line row indexing to the <basic line number>
        #    e.g. [10, 20, 30]
        # cmd_lines -> array: each command
        #    e.g. ['PRINT "START"', 'FOR I=1 TO 5', '? I', 'NEXT I', 'GOTO 20']
        # program_line_idx_to_cmd_idx -> array: each program line row indexing to cmd beginning
        #    e.g. [0, 1, 4]
        self.program = {}
        self.program_lines = None
        self.cmd_lines = None
        self.program_line_idx_to_cmd_idx = None
        self.next_cmd_run_idx = None
        self.cmd_lines_to_program_line_idx = None

        self.forloops = {}
        self.data_line = None
        self.data_index = None
        self.sleep_until = None
        self.must_run_stop = False
        if self.in_init and not self.screen.using_roms:
            # only print the basic header when we're not using actual roms
            self.screen.writestr("\n    **** commodore 64 basic v2 ****\n")
            self.screen.writestr("\n 64k ram system  38911 basic bytes free\n")
            self.write_prompt("\n")
        self.stop_running_program()

    @property
    def running_program(self):
        return self.next_cmd_run_idx is not None

    @staticmethod
    def _variables_get_internal_symbol_name(symbol, is_array):
        # limit to max two characters for identification
        if len(symbol) > 2:
            symbol = symbol[:2]
        else:
            symbol = symbol
        
        if is_array:
            return "_array_real_" + symbol
        else:
            return "_var_real_" + symbol

    def _variables_get_value(self, symbol, array_index):
        if symbol in self.symbols and array_index is None:
            return self.symbols[symbol]

        internal_symbol = self._variables_get_internal_symbol_name(symbol, True if array_index is not None else False)
        if internal_symbol not in self.symbols:
            # auto create if not found
            self._variables_assignment(symbol, array_index, 0)
        
        if array_index is not None:
            if array_index > len(self.symbols[internal_symbol])-1:
                raise BasicError("bad subscript")
            
            return self.symbols[internal_symbol][array_index]
        else:
            return self.symbols[internal_symbol]

    def _variables_assignment(self, symbol, array_index, value):
        if value is None:
            raise BasicError("syntax")

        if array_index is not None:
            internal_symbol = self._variables_get_internal_symbol_name(symbol, True)
            if internal_symbol not in self.symbols:
                # auto create if not found
                self._variables_dim_array(symbol, None)
            
            if array_index > len(self.symbols[internal_symbol])-1:
                raise BasicError("bad subscript")
            
            self.symbols[internal_symbol][array_index] = value
        else:
            internal_symbol = self._variables_get_internal_symbol_name(symbol, False)
            self.symbols[internal_symbol] = value

    def _variables_dim_array(self, symbol, size = None):
        if not size:
            # auto-dimension
            size = 10
        elif size < 1 or size > 32767:
            raise BasicError("illegal quantity")
        
        # change the internal symbol name to not collide with a non-dim'ed
        # variable with the same name
        internal_symbol = self._variables_get_internal_symbol_name(symbol, True)

        if internal_symbol in self.symbols:
            raise BasicError("REDIM'D ARRAY")

        # c64 dim'ed arrays are always size+1
        size = size + 1
        self.symbols[internal_symbol] = eval('[0]*'+str(size), self.symbols)

    def _evaluate_expression(self, expression):
        result = None
        if expression:
            tokens = self._tokenize(expression)
            result = self._parse_expression(tokens.copy())
        return result

    def _tokenize(self, expression):
        """Converts a string expression into a list of tokens."""
        # Split expression into tokens, preserving quoted strings
        quoted_string_tokens = re.findall(r'"[^"]*"|\S+', expression)
        tokens = []
        for token in quoted_string_tokens:
            if len(token) > 1 and token.startswith('"') and token.endswith('"'):
                tokens.append(token)
                continue

            token = token.replace(" ", "")
            if token == '':
                continue

            tokens.extend(list(token))

        return tokens

    def _parse_expression(self, tokens):
        """Parses a mathematical expression and returns the result."""
        value = self._parse_term(tokens)
        while tokens and tokens[0] in ["+", "-"]:
            operator = tokens.pop(0)
            term = self._parse_term(tokens)
            if operator == "+":
                value += term
            elif operator == "-":
                value -= term
        return value

    def _parse_term(self, tokens):
        """Parses a term in a mathematical expression and returns the result."""
        value = self._parse_factor(tokens)
        while tokens and tokens[0] in ["*", "/"]:
            operator = tokens.pop(0)
            factor = self._parse_factor(tokens)
            if operator == "*":
                value *= factor
            elif operator == "/":
                value /= factor
        return value

    def _parse_factor(self, tokens):
        """Parses a factor in a mathematical expression and returns the result."""
        if tokens[0] == "(":
            tokens.pop(0)  # Consume "("
            value = self._parse_expression(tokens)
            if tokens[0] != ")":
                raise ValueError("Expected ')' in expression.")
            tokens.pop(0)  # Consume ")"
        elif tokens[0].isdigit():
            value = 0
            while tokens and tokens[0].isdigit():
                value = (value * 10) + int(tokens.pop(0))
        elif tokens[0].isalpha():  # variable name must begin with alpha
            variable_name = tokens.pop(0)
            while tokens and (tokens[0].isalpha() or tokens[0].isdigit()):
                variable_name += tokens.pop(0)
            array_index = None
            if tokens and tokens[0] == "(":
                tokens.pop(0)  # Consume "("
                array_index = self._parse_expression(tokens)
                if tokens[0] != ")":
                    raise ValueError("Expected ')' in expression.")
                tokens.pop(0)  # Consume ")"
            # check for peek function
            if variable_name in ['peek', 'pE']:
                value = self.peek_func(array_index)
            else:
                # get variable with the name
                value = self._variables_get_value(variable_name, array_index)
        elif tokens[0].startswith('"') and tokens[0].endswith('"'):
            value = tokens.pop(0)[1:-1]
        else:
            raise ValueError(f"Invalid token: {tokens[0]}")
        return value

    def write_prompt(self, prefix=""):
        self.screen.writestr(prefix + "ready.\n")

    def execute_line(self, line, recursive=False):
        self.execute_cmd(line, recursive)

    def execute_cmd(self, cmd, recursive=False):
        in_program = self.running_program
        try:
            if in_program:
                # we're running in a program, REM and DATA do nothing
                if cmd.startswith(("#", "rem") or cmd.startswith(("dA", "data"))):
                    if not recursive:
                        self.next_cmd_run_idx += 1
                    return
            else:
                # direct mode
                # if there's no char on the last pos of the first line, only evaluate the first line
                # TODO does this work for single line commands????
                if len(cmd) >= self.screen.columns and cmd[self.screen.columns - 1] == ' ':
                    cmd = cmd[:self.screen.columns]
                if self.process_programline_entry(cmd):
                    return
                if cmd.startswith(("#", "rem")):
                    self.write_prompt("\n")
                    return
                if cmd.startswith(("dA", "data")):
                    raise BasicError("illegal direct")

            # execute the command(s) on the line
            if not (cmd == "" or cmd.startswith(("#", "rem", "dA", "data"))):
                do_more = self._execute_cmd(cmd.strip())
            if not recursive and not self.running_program and not self.sleep_until and not self.must_run_stop:
                self.write_prompt("\n")
            if self.running_program:
                if not recursive:
                    # schedule next cmd to be executed
                    self.next_cmd_run_idx += 1
        except GotoCmdException as gx:
            self.implementGoto(gx)            
        except FlowcontrolException:
            if in_program:
                if not recursive:
                    # we do go to the next line...
                    self.next_cmd_run_idx += 1
            raise
        except BasicError as bx:
            traceback.print_exc()
            if not self.running_program:
                self.screen.writestr("\n?" + bx.args[0].lower() + "  error\n")
                self.write_prompt()
            else:
                line = self.program_lines[self.cmd_lines_to_program_line_idx[self.next_cmd_run_idx]]
                self.screen.writestr("\n?" + bx.args[0].lower() + "  error in {line:d}\n".format(line=line))
                self.write_prompt()
            self.stop_running_program()
        except Exception as ex:
            traceback.print_exc()
            self.screen.writestr("\n?" + str(ex).lower() + "  error\n")
            self.write_prompt()
            self.stop_running_program()

    def implementGoto(self,gx: GotoCmdException):
        self.next_cmd_run_idx = gx.cmd_idx

    def process_programline_entry(self, line):
        match = re.match("(\d+)(\s*.*)", line)
        if match:
            if self.running_program:
                raise BasicError("cannot define lines while running")
            linenum, line = match.groups()
            line = line.strip()
            linenum = int(linenum)
            if not line:
                if linenum in self.program:
                    del self.program[linenum]
            else:
                self.program[linenum] = line
            return True
        return False

    def runstop(self):
        self.must_run_stop = True
        if not self.running_program:
            return
        if self.sleep_until:
            self.sleep_until = None
            line = self.program_lines[self.cmd_lines_to_program_line_idx[self.next_cmd_run_idx - 1]]
        else:
            line = self.program_lines[self.cmd_lines_to_program_line_idx[self.next_cmd_run_idx]]
        self.stop_running_program()
        self.screen.writestr("\nbreak in {:d}\n".format(line))
        self.write_prompt()

    def _execute_cmd(self, cmd):
        if cmd.startswith(("read", "rE")):
            self.execute_read(cmd)
        elif cmd.startswith(("restore", "reS")):
            self.execute_restore(cmd)
        elif cmd.startswith(("save", "sA")):
            self.execute_save(cmd)
            return False
        elif cmd.startswith(("load", "lO")):
            self.execute_load(cmd)
            return False
        elif cmd.startswith(("print", "?")):
            self.execute_print(cmd)
        elif cmd.startswith(("poke", "pO")):
            self.execute_poke(cmd)
        elif cmd.startswith(("list", "lI")):
            self.execute_list(cmd)
            return False
        elif cmd.startswith(("new", "nI")):
            self.execute_new(cmd)
            return False
        elif cmd.startswith(("run", "rU")):
            self.execute_run(cmd)
            return False
        elif cmd.startswith(("sys", "sY")):
            self.execute_sys(cmd)
        elif cmd.startswith(("goto", "gO")):
            self.execute_goto(cmd)
        elif cmd.startswith(("on")):
            self.execute_on_goto_gosub(cmd)
        elif cmd.startswith(("for", "fO")):
            self.execute_for(cmd)
        elif cmd.startswith(("next", "nE")):
            self.execute_next(cmd)
        elif cmd.startswith("if"):
            return self.execute_if(cmd)
        elif cmd.startswith(("#", "rem")):
            pass
        elif cmd.startswith(("dim", "dI")):
            self.execute_dim(cmd)
        elif cmd.startswith(("end", "eN")):
            self.execute_end(cmd)
            return False
        elif cmd.startswith(("stop", "sT")):
            self.execute_end(cmd)
            return False
        elif cmd.startswith(("get", "gE")):
            self.execute_get(cmd)
        elif cmd.startswith(("sleep", "sL")):
            self.execute_sleep(cmd)
        elif cmd.startswith(("scroll", "sC")):
            self.execute_scroll(cmd)
        elif cmd.startswith(("color", "coL")):
            self.execute_color(cmd)
        elif cmd.startswith(("cursor", "cU")):
            self.execute_cursor(cmd)
        elif cmd == "cls":
            self.screen.clear()    # basic V2:  ?chr$(147);
        elif cmd == "sync":
            self.interactive.do_sync_command()
        elif cmd == "monitor":
            self.execute_monitor(cmd)
        elif cmd.startswith("dos\""):
            self.execute_dos(cmd)
            return False
        elif cmd == "help":
            self.execute_help(cmd)
        else:
            match = re.match(r"([a-zA-Z]+[0-9]*)(\([0-9]*\))?\s*=\s*(.+)", cmd)
            if match:
                # variable assignment
                symbol, arr_index, value = match.groups()
                self._variables_assignment(symbol, self._evaluate_expression(arr_index), self._evaluate_expression(value))
                return True
            else:
                print("Syntax error:", cmd, file=sys.stderr)
                raise BasicError("syntax")
        return True

    def execute_help(self, cmd):
        self.screen.writestr("\nknown statements:\n")
        known = ["?", "print", "cls", "color", "cursor", "data", "dim", "dos", "end", "for", "get", "gopy",
                 "goto", 
                 "on...goto",
                 "if", "list", "load", "new", "next", "peek", "poke", "pokew",
                 "read", "rem", "restore", "run", "save", "scroll", "sleep", "stop", "sys", "help",
                 "monitor", "sync"]
        for kw in sorted(known):
            self.screen.writestr("{:10s}".format(kw))
        self.screen.writestr("\n")

    def execute_print(self, cmd):
        if cmd.startswith("?"):
            cmd = cmd[1:]
        elif cmd.startswith("print"):
            cmd = cmd[5:]
        print_return = "\n"
        if cmd:
            if cmd.endswith((',', ';')):
                cmd = cmd[:-1]
                print_return = ""
            result = self._evaluate_expression(cmd)
            if isinstance(result, numbers.Number):
                if result < 0:
                    result = str(result) + " "
                else:
                    result = " " + str(result) + " "
            else:
                result = str(result)
        else:
            result = ""
        self.screen.writestr(result + print_return)

    def execute_for(self, cmd):
        if cmd.startswith("fO"):
            cmd = cmd[2:]
        elif cmd.startswith("for"):
            cmd = cmd[3:]
        cmd = cmd.strip()
        match = re.match("(\w+)\s*=\s*(\S+)\s*to\s*(\S+)\s*(?:step\s*(\S+))?$", cmd)
        if match:
            if not self.running_program:
                raise BasicError("illegal direct")    # we only support for loops in a program (with line numbers), not on the screen
            varname, start, to, step = match.groups()
            if step is None:
                step = "1"
            start = self._evaluate_expression(start)
            to = self._evaluate_expression(to)
            step = self._evaluate_expression(step)

            def frange(start, to, step):
                yield start
                start += step
                if step >= 0:
                    while start <= to:
                        yield start
                        start += step
                else:
                    while start >= to:
                        yield start
                        start += step

            iterator = iter(frange(start, to, step))
            internal_varname = self._variables_get_internal_symbol_name(varname, False)
            self.forloops[internal_varname] = (self.next_cmd_run_idx, iterator)
            self.symbols[internal_varname] = next(iterator)
        else:
            raise BasicError("syntax")

    def execute_next(self, cmd):
        if cmd.startswith("nE"):
            cmd = cmd[2:]
        elif cmd.startswith("next"):
            cmd = cmd[4:]
        varname = cmd.strip()
        internal_varname = self._variables_get_internal_symbol_name(varname, False)
        if not self.running_program:
            raise BasicError("illegal direct")  # we only support for loops in a program (with line numbers), not on the screen
        if not varname:
            raise BasicError("next without varname")    # we require the varname for now
        if internal_varname not in self.forloops or internal_varname not in self.symbols:
            raise BasicError("next without for")
        if "," in internal_varname:
            raise BasicError("next with multiple vars")    # we only support one var right now
        try:
            runline_index, iterator = self.forloops[internal_varname]
            self.symbols[internal_varname] = next(iterator)
        except StopIteration:
            del self.forloops[internal_varname]
        else:
            self.next_cmd_run_idx = runline_index   # jump back to code at line after for loop

    def execute_get(self, cmd):
        if cmd.startswith("gE"):
            cmd = cmd[2:]
        elif cmd.startswith("get"):
            cmd = cmd[3:]
        if not self.running_program:
            raise BasicError("illegal direct")
        varname = cmd.strip()
        if not varname:
            raise BasicError("syntax")
        self.symbols[varname] = self.interactive.do_get_command()

    def execute_goto(self, cmd):
        if cmd.startswith("gO"):
            cmd = cmd[2:]
        elif cmd.startswith("goto"):
            cmd = cmd[4:]
        line = self._evaluate_expression(cmd)    # allows jump tables via GOTO VAR
        if not self.running_program:
            # do a run instead
            self.execute_run("run " + str(line))
        else:
            if line not in self.program:
                raise BasicError("undef'd statement")
            # go to the line previous as the program counter will be updated after this call
            raise GotoCmdException(self.program_line_idx_to_cmd_idx[self.program_lines.index(line)])
    """
    on <index-1-based> goto|gosub <line1>,<line2> 
    if index evaluate to 1 the execution proceed on line1

    """            
    def execute_on_goto_gosub(self,cmd):
        gosub=False
        if cmd.startswith("on"):
            cmd=cmd[2:]
        if cmd.find("goto")==-1 and cmd.find("gosub")==-1:
            raise BasicError("syntax")
        else:
            # Find out index list
            l2=(cmd[(cmd.find("go")+2):]).strip()
            # DEBUG print(l2)
            if l2.startswith("to"):
                # goto branch
                gosub=False
                targetLineList=l2[2:]
            elif l2.startswith("sub"):
                gosub=True
                targetLineList=l2[3:]
            else:
                raise BasicError("syntax")
        lineTargetTuple=targetLineList.strip().split(",")        
        goInx=cmd.find("go")
        expr=cmd[0:goInx]        
        # eval the on <expr> goto part
        onGoIndex=int(self._evaluate_expression(expr))-1        
        line=int(lineTargetTuple[onGoIndex])
        if gosub==False:
            if not self.running_program:
                self.execute_run("run " + str(line))
            else:
                if line not in self.program:
                    raise BasicError("undef'd statement")
                raise GotoCmdException(self.program_line_idx_to_cmd_idx[self.program_lines.index(line)])
        else:
            raise BasicError("gosub unsupported yet")
            # raise BasicError("syntax")

    def execute_sleep(self, cmd):
        if cmd.startswith("sL"):
            cmd = cmd[2:]
        elif cmd.startswith("sleep"):
            cmd = cmd[5:]
        howlong = self._evaluate_expression(cmd)
        if howlong == 0:
            return
        if 0 < howlong <= 60:       # sleep value must be between 0 and 60 seconds
            self.sleep_until = time.time() + howlong
        else:
            raise BasicError("illegal quantity")

    def execute_scroll(self, cmd):
        # scroll [direction][,fillchar][,fillcolor][,amount] OR scroll direction,x1,y1,x2,y2[,fillchar][,fillcolor][,amount]
        if cmd.startswith("sC"):
            cmd = cmd[2:]
        elif cmd.startswith("scroll"):
            cmd = cmd[6:]
        direction = eval("(" + cmd + ")", self.symbols)
        scrolldir = 'u'
        x1, y1 = 0, 0
        x2, y2 = self.screen.columns - 1, self.screen.rows - 1
        fillsc = 32
        amount = 1
        fillcolor = self.screen.text
        if type(direction) is str:
            scrolldir = direction
        else:
            if len(direction) >= 5:
                scrolldir, x1, y1, x2, y2 = direction[0:5]
                if len(direction) >= 6:
                    fillsc = direction[5]
                if len(direction) >= 7:
                    fillcolor = direction[6]
                if len(direction) >= 8:
                    amount = direction[7]
                if len(direction) > 8:
                    raise BasicError("syntax")
            else:
                if len(direction) >= 1:
                    scrolldir = direction[0]
                if len(direction) >= 2:
                    fillsc = direction[1]
                if len(direction) >= 3:
                    fillcolor = direction[2]
                if len(direction) >= 4:
                    amount = direction[3]
                if len(direction) > 4:
                    raise BasicError("syntax")
        if x1 < 0 or x1 >= self.screen.columns or x2 < 0 or x2 >= self.screen.columns or\
                y1 < 0 or y1 >= self.screen.rows or y2 < 0 or y2 >= self.screen.rows:
            raise BasicError("illegal quantity")
        if amount <= 0 or amount > max(self.screen.columns, self.screen.rows):
            raise BasicError("illegal quantity")
        if scrolldir in ("u", "d", "l", "r", "ul", "ur", "dl", "dr", "lu", "ru", "ld", "rd"):
            self.screen.scroll((x1, y1), (x2, y2),
                               'u' in scrolldir, 'd' in scrolldir, 'l' in scrolldir, 'r' in scrolldir,
                               (fillsc, fillcolor), amount)
        else:
            raise BasicError("scroll direction")

    def execute_end(self, cmd):
        if cmd not in ("eN", "end", "sT", "stop"):
            raise BasicError("syntax")
        if self.running_program:
            if cmd in ("sT", "stop"):
                self.screen.writestr("\nbreak in {:d}\n".format(
                    self.program_lines[self.cmd_lines_to_program_line_idx[self.next_cmd_run_idx]]
                ))
            self.stop_running_program()

    def execute_poke(self, cmd):
        if cmd.startswith("pO"):
            cmd = cmd[2:]
        elif cmd.startswith("poke"):
            cmd = cmd[4:]
        addr, value = cmd.split(',', maxsplit=1)
        addr, value = self._evaluate_expression(addr), int(self._evaluate_expression(value))
        if addr < 0 or addr > 0xffff or value < 0 or value > 0xff:
            raise BasicError("illegal quantity")
        self.screen.memory[int(addr)] = int(value)

    def execute_pokew(self, cmd):
        # 16-bits poke
        if cmd.startswith("pokew"):
            cmd = cmd[5:]
        addr, value = cmd.split(',', maxsplit=1)
        addr, value = self._evaluate_expression(addr), int(self._evaluate_expression(value))
        if addr < 0 or addr > 0xffff or addr & 1 or value < 0 or value > 0xffff:
            raise BasicError("illegal quantity")
        self.screen.memory.setword(int(addr), int(value))

    def execute_sys(self, cmd):
        if cmd.startswith("sY"):
            cmd = cmd[2:]
        elif cmd.startswith("sys"):
            cmd = cmd[3:]
        if not cmd:
            raise BasicError("syntax")
        addr = self._evaluate_expression(cmd)
        try:
            do_sys(self.screen, addr, self.interactive._microsleep)
        except FlowcontrolException:
            raise
        except Exception as x:
            raise BasicError(str(x))

    def peek_func(self, address):
        if address < 0 or address > 0xffff:
            raise BasicError("illegal quantity")
        return self.screen.memory[address]

    def peekw_func(self, address):
        if address < 0 or address > 0xffff or address & 1:
            raise BasicError("illegal quantity")
        return self.screen.memory.getword(address)
    
    def execute_dim(self, cmd):
        if cmd.startswith("dI"):
            cmd = cmd[2:]
        elif cmd.startswith("dim"):
            cmd = cmd[3:]

        match = re.match(r"^\s*([a-zA-Z][a-zA-Z0-9]*)(\([0-9]*\))?\s*$", cmd)
        if not match:
            raise BasicError("syntax")

        symbol, arrSize = match.groups()

        size = None
        if arrSize:
            if len(arrSize) < 3:
                raise BasicError("syntax")
            size = int(arrSize[1:-1])

        self._variables_dim_array(symbol, size)

    def execute_list(self, cmd):
        if cmd.startswith("lI"):
            cmd = cmd[2:]
        elif cmd.startswith("list"):
            cmd = cmd[4:]
        start, sep, to = cmd.partition("-")
        start = start.strip()
        if to:
            to = to.strip()
        if not self.program:
            return
        if start and not to and not sep:
            to = start
        start = int(start) if start else 0
        to = int(to) if to else None
        self.must_run_stop = False
        self.screen.writestr("\n")
        for num, text in sorted(self.program.items()):
            if num < start:
                continue
            if to is not None and num > to:
                break
            self.screen.writestr("{:d} {:s}\n".format(num, text))
            if self.must_run_stop:
                self.screen.writestr("break\n")
                break
            self.interactive.do_sync_command()

    def execute_new(self, cmd):
        if cmd.startswith("nE"):
            cmd = cmd[2:]
        elif cmd.startswith("new"):
            cmd = cmd[3:]
        if cmd:
            raise BasicError("syntax")
        self.reset()

    def execute_save(self, cmd):
        if cmd.startswith("sA"):
            cmd = cmd[2:]
        elif cmd.startswith("save"):
            cmd = cmd[4:]
        cmd = cmd.strip()
        if cmd.endswith("\",8,1"):
            cmd = cmd[:-4]
        elif cmd.endswith("\",8"):
            cmd = cmd[:-2]
        if not (cmd.startswith('"') and cmd.endswith('"')):
            raise BasicError("syntax")
        cmd = cmd[1:-1]
        if not cmd:
            raise BasicError("missing file name")
        if not self.program:
            return
        if not cmd.endswith(".bas"):
            cmd += ".bas"
        self.screen.writestr("\nsaving " + cmd)
        with open("drive8/" + cmd, "w", encoding="utf8") as file:
            file.writelines("{:d} {:s}\n".format(num, line) for num, line in sorted(self.program.items()))

    def execute_load(self, cmd):
        if cmd.startswith("lO"):
            cmd = cmd[2:]
        elif cmd.startswith("load"):
            cmd = cmd[4:]
        try:
            program = do_load(self.screen, cmd)
        except Exception as x:
            raise BasicError(str(x))
        if program and not isinstance(program, dict):
            raise BasicError("invalid file type")
        self.program = program

    def execute_dos(self, cmd):
        # to show floppy contents without clobbering basic program like LOAD"$",8 would
        cmd = cmd[4:]
        do_dos(self.screen, cmd)

    def execute_run(self, cmd):
        cmd = cmd[3:]
        start = int(cmd) if cmd else None
        if start is not None and start not in self.program:
            raise BasicError("undef'd statement")
        if self.program:
            self.data_line = None
            self.data_index = None
            self.program_lines = list(sorted(self.program))
            self.cmd_lines = []
            self.program_line_idx_to_cmd_idx = {}
            self.cmd_lines_to_program_line_idx = []
            for program_line_idx, line_number in enumerate(self.program_lines):
                line = self.program[line_number]
                self.program_line_idx_to_cmd_idx[program_line_idx] = len(self.cmd_lines)
                for cmd in [x for x in (p.strip() for p in line.split(":")) if x]:
                    self.cmd_lines.append(cmd)
                    self.cmd_lines_to_program_line_idx.append(program_line_idx)

            raise GotoCmdException(0 if start is None else self.program_line_idx_to_cmd_idx[self.program_lines.index(start)])

    def _parse_if_condition(self, if_condition):
        operators = ['<','>','<=','>=','=']
        operator = None
        tokens = None
        for operator in operators:
            tokens = if_condition.split(operator)
            if len(tokens) == 2:
                break

        if len(tokens) < 1 or len(tokens) > 2:
            raise BasicError('syntax')

        result = False
        if len(tokens) == 1:
            result = self._evaluate_expression(tokens[0])
            if result:
                result = True
            else:
                result = False
        else:
            left_value = self._evaluate_expression(tokens[0])
            right_value = self._evaluate_expression(tokens[1])
            if operator == '<':
                result = left_value < right_value 
            elif operator == '>':
                result = left_value > right_value 
            elif operator == '<=':
                result = left_value <= right_value 
            elif operator == '>=':
                result = left_value >= right_value 
            elif operator == '=':
                result = left_value == right_value 

        return result

    def execute_if(self, cmd):
        match = re.match(r"if(.+)then(.+)$", cmd)
        if match:
            condition, then = match.groups()
            condition = self._evaluate_expression(condition)
            if condition:
                return self.execute_cmd(then, recursive=True)
        else:
            # perhaps if .. goto .. form?
            match = re.match(r"if(.+)goto\s+(\S+)$", cmd)
            if not match:
                raise BasicError("syntax")
            condition, line = match.groups()
            condition = self._evaluate_expression(condition)
            if condition:
                line = self._evaluate_expression(line)   # allows jumptables via GOTO VAR
                if line not in self.program:
                    raise BasicError("undef'd statement")
                raise GotoCmdException(self.program_line_idx_to_cmd_idx[self.program_lines.index(line)])
        return True

    def execute_read(self, cmd):
        if cmd.startswith("rE"):
            cmd = cmd[2:]
        elif cmd.startswith("read"):
            cmd = cmd[4:]
        varname = cmd.strip()
        if ',' in varname:
            raise BasicError("syntax")
        internal_varname = self._variables_get_internal_symbol_name(varname, None)
        value = self.get_next_data()
        if value is None:
            raise BasicError("out of data")
        self.symbols[internal_varname] = value

    def execute_restore(self, cmd):
        if cmd.startswith("reS"):
            cmd = cmd[3:]
        elif cmd.startswith("restore"):
            cmd = cmd[7:]
        if cmd:
            raise BasicError("syntax")
        self.data_line = None
        self.data_index = None

    def execute_color(self, cmd):
        # BASIC V2 equivalent:  poke 53280,c0: poke 53281, c1: poke 646, c2
        if cmd.startswith("coL"):
            cmd = cmd[3:]
        elif cmd.startswith("color"):
            cmd = cmd[5:]
        if cmd:
            colors = eval(cmd, self.symbols)
            if isinstance(colors, tuple):
                if len(colors) != 3:
                    raise BasicError("syntax")
                c1 = int(colors[0])
                c2 = int(colors[1])
                c3 = int(colors[2])
                if c1 > 255 or c2 > 255 or c3 > 255:
                    raise BasicError("illegal quantity")
                self.screen.border = c1
                self.screen.screen = c2
                self.screen.text = c3
                return
        raise BasicError("syntax")

    def execute_cursor(self, cmd):
        # BASIC V2 equivalent:  poke 211,x: poke 214,y: sys 58640
        if cmd.startswith("cU"):
            cmd = cmd[2:]
        elif cmd.startswith("cursor"):
            cmd = cmd[6:]
        if cmd:
            coords = eval(cmd, self.symbols)
            if isinstance(coords, tuple):
                if len(coords) != 2:
                    raise BasicError("syntax")
                x = int(coords[0]) % self.screen.columns
                y = int(coords[1]) % self.screen.rows
                self.screen.cursormove(x, y)
                return
        raise BasicError("syntax")

    def execute_monitor(self, cmd):
        if cmd.startswith("monitor"):
            cmd = cmd[7:]
        self.screen.writestr("starting monitor...(see console window)\n")
        self.screen.shifted = True
        from .cputools import Monitor
        stdout = StdoutWrapper(self.screen, duplicate=sys.stdout)
        mon = Monitor(memory=self.screen.memory, stdout=stdout)
        mon.onecmd("version")
        mon.cmdloop()
        self.screen.writestr("...back from monitor.\n")

    def stop_running_program(self):
        if self.running_program:
            self.next_cmd_run_idx = None
        self.sleep_until = None

    def get_next_data(self):
        if self.data_line is None:
            # search first data statement in program
            self.data_index = 0
            for nr, line in sorted(self.program.items()):
                if line.lstrip().startswith(("dA", "data")):
                    self.data_line = nr
                    break
            else:
                return None
        try:
            data = self.program[self.data_line].split(maxsplit=1)[1]
            value = data.split(",")[self.data_index]
        except IndexError:
            # go to next line
            self.data_index = 0
            for nr, line in sorted(self.program.items()):
                if self.data_line < nr and line.lstrip().startswith(("dA", "data")):
                    self.data_line = nr
                    return self.get_next_data()
            else:
                return None
        else:
            self.data_index += 1
            return self._evaluate_expression(value)

    def program_step(self):
        # perform a discrete step of the running program
        if not self.running_program:
            return   # no program currently running
        if self.sleep_until is not None:
            # we're in a sleep call!
            if time.time() < self.sleep_until:
                return []
            self.sleep_until = None
        if self.next_cmd_run_idx >= len(self.cmd_lines):
            self.write_prompt("\n")
            self.stop_running_program()
        else:
            self.execute_cmd(self.cmd_lines[self.next_cmd_run_idx])
