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

import math
import sys
import platform
import traceback
import re
import time
import numbers
from .shared import StdoutWrapper, do_load, do_dos, do_sys, FlowcontrolException

# Credit for the ascToPetTable: https://github.com/AndiB/PETSCIItoASCII
ascToPetTable = [
    0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x14,0x20,0x0d,0x11,0x93,0x0a,0x0e,0x0f,
    0x10,0x0b,0x12,0x13,0x08,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
    0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
    0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
    0x40,0xc1,0xc2,0xc3,0xc4,0xc5,0xc6,0xc7,0xc8,0xc9,0xca,0xcb,0xcc,0xcd,0xce,0xcf,
    0xd0,0xd1,0xd2,0xd3,0xd4,0xd5,0xd6,0xd7,0xd8,0xd9,0xda,0x5b,0x5c,0x5d,0x5e,0x5f,
    0xc0,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,
    0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5a,0xdb,0xdc,0xdd,0xde,0xdf,
    0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87,0x88,0x89,0x8a,0x8b,0x8c,0x8d,0x8e,0x8f,
    0x90,0x91,0x92,0x0c,0x94,0x95,0x96,0x97,0x98,0x99,0x9a,0x9b,0x9c,0x9d,0x9e,0x9f,
    0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,0xa8,0xa9,0xaa,0xab,0xac,0xad,0xae,0xaf,
    0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,0xb8,0xb9,0xba,0xbb,0xbc,0xbd,0xbe,0xbf,
    0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,
    0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f,
    0xe0,0xe1,0xe2,0xe3,0xe4,0xe5,0xe6,0xe7,0xe8,0xe9,0xea,0xeb,0xec,0xed,0xee,0xef,
    0xf0,0xf1,0xf2,0xf3,0xf4,0xf5,0xf6,0xf7,0xf8,0xf9,0xfa,0xfb,0xfc,0xfd,0xfe,0xff
]

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

    def _variables_get_internal_symbol_name(self, symbol):
        match = re.match(r'([a-zA-Z][a-zA-Z0-9]*\$?)(\(\d*\))?', symbol)
        if not match:
            raise BasicError('syntax')
        varname, array_index = match.groups()
        if array_index:
            # strip off the r'(d*)'
            symbol = varname
            array_index = self._evaluate_expression(array_index)

        variable_type = 'real'
        if varname.endswith('$'):
            variable_type = 'str'
            varname = varname[:-1]

        # limit to max two characters for identification
        varname = varname[:2] if len(varname) > 2 else varname

        if array_index:
            result = f'_array_{variable_type}_' + symbol
        else:
            result = f'_var_{variable_type}_' + symbol

        return result, array_index

    def _variables_get_value(self, symbol):
        if symbol in self.symbols:
            return self.symbols[symbol]

        internal_symbol, array_index = self._variables_get_internal_symbol_name(symbol)
        if internal_symbol not in self.symbols:
            # auto create if not found
            self._variables_assignment(symbol, None)
        
        if array_index is not None:
            # TODO fix this
            if array_index > len(self.symbols[internal_symbol])-1:
                raise BasicError("bad subscript")
            
            return self.symbols[internal_symbol][array_index]
        else:
            return self.symbols[internal_symbol]

    def _variables_assignment(self, symbol, value):
        internal_symbol, array_index = self._variables_get_internal_symbol_name(symbol)

        if value is None:
            if '_str_' in internal_symbol:
                value = ''
            elif '_real_' in internal_symbol:
                value = 0
            else:
                raise BasicError('internal consistency')

        if '_str_' in internal_symbol and type(value) is not str:
            raise BasicError("syntax")
        if '_real_' in internal_symbol and not (type(value) in [int, float]):
            raise BasicError("syntax")

        if array_index is not None:
            if internal_symbol not in self.symbols:
                # auto create if not found
                self._variables_dim_array(symbol, None)

            # TODO fix this
            if array_index > len(self.symbols[internal_symbol])-1:
                raise BasicError("bad subscript")
            
            self.symbols[internal_symbol][array_index] = value
        else:
            self.symbols[internal_symbol] = value

    def _variables_dim_array(self, symbol, size = None):
        if not size:
            # auto-dimension
            size = 10
        elif size < 1 or size > 32767:
            raise BasicError("illegal quantity")
        
        # change the internal symbol name to not collide with a non-dim'ed
        # variable with the same name
        internal_symbol, array_index = self._variables_get_internal_symbol_name(symbol)

        if internal_symbol in self.symbols:
            raise BasicError("REDIM'D ARRAY")

        # c64 dim'ed arrays are always size+1
        size = size + 1
        self.symbols[internal_symbol] = eval('[0]*'+str(size), self.symbols)

    def _evaluate_expression(self, expression, must_be_variable_assignment=False):
        result = None
        if must_be_variable_assignment:
            match = re.match(r"([a-zA-Z]+[0-9]*)(\$)?(\([a-zA-Z0-9]*\))?\s*=\s*(.+)", expression)
            if match:
                # variable assignment
                symbol, string_identifier, index_expression, value = match.groups()
                symbol += string_identifier if string_identifier else ''
                arr_index = None
                if index_expression:
                    arr_index = self._evaluate_expression(index_expression)
                # add on the array index (if supplied)
                symbol = f'{symbol}({arr_index})' if arr_index is not None else symbol
                self._variables_assignment(symbol, self._evaluate_expression(value))
                return None
            else:
                print("Syntax error:", expression, file=sys.stderr)
                raise BasicError("syntax")

        if expression:
            tokens = self._tokenize(expression)

            # determine if expression is a comparison or just return a value
            op_idx = None
            for operator in ['<=', '>=', '<>', '<', '>', '=']:
                if operator in tokens:
                    op_idx = tokens.index(operator)
                    break

            if op_idx:
                if op_idx == 0 or (op_idx == len(tokens)-1):
                    raise BasicError('syntax')
                left_value = self._parse_expression(tokens[:op_idx].copy())
                right_value = self._parse_expression(tokens[op_idx+1:].copy())
                if operator == '<':
                    result = -1 if left_value < right_value else 0
                elif operator == '>':
                    result = -1 if left_value > right_value else 0
                elif operator == '<=':
                    result = -1 if left_value <= right_value else 0
                elif operator == '>=':
                    result = -1 if left_value >= right_value else 0
                elif operator == '<>':
                    result = -1 if not (left_value == right_value) else 0
                elif operator == '=':
                    result = -1 if left_value == right_value else 0
            else:
                result = self._parse_expression(tokens.copy())
        return result

    def _tokenize(self, expression):
        """Converts a string expression into a list of tokens."""
        # Split expression into tokens, preserving quoted strings
        quoted_string_tokens = re.findall(r'"[^"]*"|<>|<=|>=|<|>|=|\+|-|\*|/|\(|\)|\d+|[A-Za-z]\w*\$?(?:\(\d*\))?', expression)
        tokens = []
        for token in quoted_string_tokens:
            if len(token) > 1 and token.startswith('"') and token.endswith('"'):
                tokens.append(token)
                continue

            if token in ['>=', '<=', '<>']:
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
                if type(value) is str and type(term) is not str:
                    raise BasicError("type mismatch")
                if type(value) in [int, float] and type(term) not in [int, float]:
                    raise BasicError("type mismatch")

                value += term
            elif operator == "-":
                # strings cannot be subtracted from each other
                if type(value) is str or type(term) is str:
                    raise BasicError("type mismatch")
                value -= term
        return value

    def _parse_term(self, tokens):
        """Parses a term in a mathematical expression and returns the result."""
        value = self._parse_factor(tokens)
        while tokens and tokens[0] in ["*", "/"]:
            operator = tokens.pop(0)
            factor = self._parse_factor(tokens)

            # strings cannot be operated on
            if type(value) is str or type(factor) is str:
                raise BasicError("type mismatch")

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
            match = re.match(r"([a-zA-Z]+[0-9]*)(\$)?(\(\"?[a-zA-Z0-9]*\"?\))?(.+)?", ''.join(tokens))
            if not match:
                raise BasicError('syntax')

            variable_name, string_type, index_expression, remainder = match.groups()
            if variable_name:
                [tokens.pop(0) for idx in range(len(variable_name))]
            if string_type:
                [tokens.pop(0) for idx in range(len(string_type))]
            if index_expression:
                # re-tokenize to count quoted strings groupings properly
                [tokens.pop(0) for idx in range(len(self._tokenize(index_expression)))]

            # check for the peek function (as it returns back a value)
            if variable_name in ['peek', 'pE']:
                value = self.peek_func(self._evaluate_expression(index_expression))
            elif variable_name in ['asc']:
                value = self.asc_func(self._evaluate_expression(index_expression))
            else:
                # add on the string_type (if available)
                if string_type:
                    variable_name += string_type
                # add on the index (if available)
                if index_expression:
                    variable_name += '(' + str(self._evaluate_expression(index_expression)) + ')'
                value = self._variables_get_value(variable_name)
                # value = self._variables_get_value(variable_name + (index if index else ''))
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
            self._evaluate_expression(cmd, True)
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
            internal_varname, array_index = self._variables_get_internal_symbol_name(varname)
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
        internal_varname, array_index = self._variables_get_internal_symbol_name(varname)
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
        internal_varname, array_index = self._variables_get_internal_symbol_name(varname)
        self.symbols[internal_varname] = self.interactive.do_get_command()

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
        if type(address) is not int:
            raise BasicError('type mismatch')
        if address < 0 or address > 0xffff:
            raise BasicError("illegal quantity")
        return self.screen.memory[address]

    def asc_func(self, ascii):
        if type(ascii) is not str:
            raise BasicError('type mismatch')
        if ascii == '':
            raise BasicError('illegal quantity')
        return ascToPetTable[ord(ascii[0]) & 0xff]

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

    def execute_if(self, cmd):
        match = re.match(r"if(.+)\s*(then|goto)\s*(.+)$", cmd)
        if match:
            condition, verb, action = match.groups()
            condition = self._evaluate_expression(condition)
            if condition:
                if action[0].isdigit():
                    # can be THEN or GOTO
                    try:
                        line = int(action)
                        if line not in self.program:
                            raise BasicError("undef'd statement")
                        raise GotoCmdException(self.program_line_idx_to_cmd_idx[self.program_lines.index(line)])
                    except ValueError:
                        raise BasicError('syntax')
                else:
                    if verb == "goto":
                        raise BasicError('syntax')
                    return self.execute_cmd(action, recursive=True)
        return True

    def execute_read(self, cmd):
        if cmd.startswith("rE"):
            cmd = cmd[2:]
        elif cmd.startswith("read"):
            cmd = cmd[4:]
        varname = cmd.strip()
        if ',' in varname:
            raise BasicError("syntax")
        internal_varname, array_index = self._variables_get_internal_symbol_name(varname)
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

