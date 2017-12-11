#! /usr/bin/env python3

"""
Intermediate Language for 6502/6510 microprocessors

Written by Irmen de Jong (irmen@razorvine.net)
License: GNU GPL 3.0, see LICENSE
"""

import os
import io
import datetime
import subprocess
import contextlib
import argparse
from functools import partial
from typing import TextIO, Dict, Set, Union
from parse import ProgramFormat, Parser, ParseResult, Optimizer
from symbols import Zeropage, DataType, VariableDef, REGISTER_BYTES, REGISTER_WORDS


class CodeError(Exception):
    pass


class CodeGenerator:
    def __init__(self, parsed: ParseResult) -> None:
        self.parsed = parsed
        self.generated_code = io.StringIO()
        self.p = partial(print, file=self.generated_code)
        self.reg_values = {}    # type: Dict[str, Union[int, str]]   # track register a/x/y values to avoid duplicate loads
        self.previous_stmt_was_assignment = False
        self.cur_block = None    # type: ParseResult.Block

    def generate(self) -> None:
        self.sanitycheck()
        self.header()
        self.initialize_variables()
        self.blocks()
        self.footer()

    def sanitycheck(self) -> None:
        # duplicate block names?
        all_blocknames = [b.name for b in self.parsed.blocks if b.name]
        unique_blocknames = set(all_blocknames)
        if len(all_blocknames) != len(unique_blocknames):
            for name in unique_blocknames:
                all_blocknames.remove(name)
            raise CodeError("there are duplicate block names", all_blocknames)
        # ZP block contains no code?
        for zpblock in [b for b in self.parsed.blocks if b.name == "ZP"]:
            if zpblock.label_names:
                raise CodeError("ZP block cannot contain labels")
            if zpblock.statements:
                raise CodeError("ZP block cannot contain code statements")

    def optimize(self) -> None:
        # optimize the generated assembly code
        pass

    def write_assembly(self, out: TextIO) -> None:
        out.write(self.generated_code.getvalue())

    def header(self) -> None:
        self.p("; code generated by il65.py")
        self.p("; source file:", self.parsed.sourcefile)
        if self.parsed.with_sys:
            self.p("; output format:", self.parsed.format.value, " (with basic program SYS)")
        else:
            self.p("; output format:", self.parsed.format.value)
        self.p("; assembler syntax is for 64tasm")
        self.p(".cpu '6502'\n.enc 'none'\n")
        if self.parsed.format == ProgramFormat.PRG:
            if self.parsed.with_sys:
                self.p("; ---- basic program with sys call ----")
                self.p("* = " + self.to_hex(self.parsed.start_address))
                year = datetime.datetime.now().year
                self.p("\t\t.word (+), {:d}".format(year))
                self.p("\t\t.null $9e, format(' %d ', _il65_sysaddr), $3a, $8f, ' il65 by idj'")
                self.p("+\t\t.word 0")
                self.p("_il65_sysaddr\t\t; assembly code starts here\n")
            else:
                self.p("; ---- program without sys call ----")
                self.p("* = " + self.to_hex(self.parsed.start_address) + "\n")
        if self.parsed.format == ProgramFormat.RAW:
            self.p("; ---- raw assembler program ----")
            self.p("* = " + self.to_hex(self.parsed.start_address) + "\n")

    @staticmethod
    def to_hex(number: int) -> str:
        # 0..255 -> "$00".."$ff"
        # 256..65536 -> "$0100".."$ffff"
        if 0 <= number < 0x100:
            return "${:02x}".format(number)
        if number < 0x10000:
            return "${:04x}".format(number)
        raise OverflowError(number)

    def initialize_variables(self) -> None:
        must_save_zp = self.parsed.clobberzp and self.parsed.restorezp
        if must_save_zp:
            self.p("; save zp")
            self.p("\t\tsei")
            self.p("\t\tldx #2")
            self.p("-\t\tlda $00,x")
            self.p("\t\tsta _il65_zp_backup-2,x")
            self.p("\t\tinx")
            self.p("\t\tbne -")

        # Only the vars from the ZeroPage need to be initialized here,
        # the vars in all other blocks are just defined and pre-filled there.
        # The iteration over the variables has a specific sort order to optimize init sequence
        zpblocks = [b for b in self.parsed.blocks if b.name == "ZP"]
        if zpblocks:
            assert len(zpblocks) == 1
            zpblock = zpblocks[0]
            vars_to_init = list(sorted(v for v in zpblock.symbols.iter_variables()
                                if v.allocate and v.type in (DataType.BYTE, DataType.WORD, DataType.FLOAT)))
            prev_value = 0  # type: Union[str, int, float]
            if vars_to_init:
                self.p("; init zp vars")
                self.p("\t\tlda #0\n\t\tldx #0")
                for variable in vars_to_init:
                    vname = zpblock.label + "." + variable.name
                    vvalue = variable.value
                    if variable.type == DataType.BYTE:
                        if vvalue != prev_value:
                            self.p("\t\tlda #${:02x}".format(vvalue))
                            prev_value = vvalue
                        self.p("\t\tsta {:s}".format(vname))
                    elif variable.type == DataType.WORD:
                        if vvalue != prev_value:
                            self.p("\t\tlda #<${:04x}".format(vvalue))
                            self.p("\t\tldx #>${:04x}".format(vvalue))
                            prev_value = vvalue
                        self.p("\t\tsta {:s}".format(vname))
                        self.p("\t\tstx {:s}+1".format(vname))
                    elif variable.type == DataType.FLOAT:
                        raise TypeError("floats cannot be stored in the zp")
                self.p("; end init zp vars")
            else:
                self.p("\t\t; there are no zp vars to initialize")
        else:
            self.p("\t\t; there is no zp block to initialize")
        main_block_label = [b.label for b in self.parsed.blocks if b.name == "main"][0]
        if must_save_zp:
            self.p("\t\tjsr {:s}.start\t\t; call user code".format(main_block_label))
            self.p("; restore zp")
            self.p("\t\tcld")
            self.p("\t\tphp\n\t\tpha\n\t\ttxa\n\t\tpha\n\t\tsei")
            self.p("\t\tldx #2")
            self.p("-\t\tlda _il65_zp_backup-2,x")
            self.p("\t\tsta $00,x")
            self.p("\t\tinx")
            self.p("\t\tbne -")
            self.p("\t\tcli\n\t\tpla\n\t\ttax\n\t\tpla\n\t\tplp")
            self.p("\t\trts")
            self.p("_il65_zp_backup\t\t.fill 254, 0")
        else:
            self.p("\t\tjmp {:s}.start\t\t; call user code".format(main_block_label))

    def blocks(self) -> None:
        # if there's a Zeropage block, it always goes first
        for zpblock in [b for b in self.parsed.blocks if b.name == "ZP"]:
            assert not zpblock.statements
            self.cur_block = zpblock
            self.p("\n; ---- zero page block: '{:s}' ----\t\t; src l. {:d}\n".format(zpblock.name, zpblock.linenum))
            self.p("{:s}\t.proc\n".format(zpblock.label))
            self.generate_block_vars(zpblock)
            self.p("\t.pend\n")
        # make sure the main.start routine clears the decimal and carry flags as first steps
        for block in self.parsed.blocks:
            if block.name == "main":
                statements = list(block.statements)
                for index, stmt in enumerate(statements):
                    if isinstance(stmt, ParseResult.Label) and stmt.name == "start":
                        asmlines = [
                            "\t\tcld\t\t\t; clear decimal flag",
                            "\t\tclc\t\t\t; clear carry flag"
                        ]
                        statements.insert(index+1, ParseResult.InlineAsm(0, asmlines))
                        break
                block.statements = statements
        # generate
        for block in sorted(self.parsed.blocks, key=lambda b: b.address):
            if block.name == "ZP":
                continue    # zeropage block is already processed
            self.cur_block = block
            self.p("\n; ---- next block: '{:s}' ----\t\t; src l. {:d}\n".format(block.name, block.linenum))
            if block.address:
                self.p(".cerror * > ${0:04x}, 'block address overlaps by ', *-${0:04x},' bytes'".format(block.address))
                self.p("* = ${:04x}".format(block.address))
            self.p("{:s}\t.proc\n".format(block.label))
            self.generate_block_vars(block)
            subroutines = list(block.symbols.iter_subroutines())
            if subroutines:
                self.p("\n; external subroutines")
                for subdef in subroutines:
                    self.p("\t\t{:s} = {:s}".format(subdef.name, self.to_hex(subdef.address)))
                self.p("; end external subroutines")
            for stmt in block.statements:
                self.generate_statement(stmt)
            self.p("\t.pend\n")

    def generate_block_vars(self, block: ParseResult.Block) -> None:
        if self.parsed.format == ProgramFormat.PRG:
            self.p("_il65_addr_save = *")
        mem_vars = [vi for vi in block.symbols.iter_variables() if not vi.allocate and not vi.register]
        if mem_vars:
            self.p("; memory mapped variables")
            for vardef in mem_vars:
                # create a definition for variables at a specific place in memory (memory-mapped)
                if vardef.type in (DataType.BYTE, DataType.WORD, DataType.FLOAT):
                    self.p("\t\t{:s} = {:s}".format(vardef.name, self.to_hex(vardef.address)))
                elif vardef.type == DataType.BYTEARRAY:
                    self.p("* = {:s}".format(self.to_hex(vardef.address)))
                    self.p("{:s}\t\t.fill {:d}".format(vardef.name, vardef.length))
                elif vardef.type == DataType.WORDARRAY:
                    self.p("* = {:s}".format(self.to_hex(vardef.address)))
                    self.p("{:s}\t\t.fill {:d}\t\t; {:d} words".format(vardef.name, vardef.length * 2, vardef.length))
                elif vardef.type == DataType.MATRIX:
                    self.p("* = {:s}".format(self.to_hex(vardef.address)))
                    self.p("{:s}\t\t.fill {:d}\t\t; matrix {:d}*{:d} bytes".format(vardef.name,
                                                                                   vardef.matrixsize[0] * vardef.matrixsize[1],
                                                                                   vardef.matrixsize[0], vardef.matrixsize[1]))
                else:
                    raise ValueError("invalid var type")
        if self.parsed.format == ProgramFormat.PRG:
            self.p("* = _il65_addr_save")
        non_mem_vars = [vi for vi in block.symbols.iter_variables() if vi.allocate]
        if non_mem_vars:
            self.p("; normal variables")
            for vardef in non_mem_vars:
                # create a definition for a variable that takes up space and will be initialized at startup
                if vardef.type in (DataType.BYTE, DataType.WORD, DataType.FLOAT):
                    if vardef.address:
                        assert block.name == "ZP", "only ZP-variables can be put on an address"
                        self.p("\t\t{:s} = {:s}".format(vardef.name, self.to_hex(vardef.address)))
                    else:
                        if vardef.type == DataType.BYTE:
                            self.p("{:s}\t\t.byte {:s}".format(vardef.name, self.to_hex(int(vardef.value))))
                        elif vardef.type == DataType.WORD:
                            self.p("{:s}\t\t.word {:s}".format(vardef.name, self.to_hex(int(vardef.value))))
                        elif vardef.type == DataType.FLOAT:
                            self.p("{:s}\t\t.byte 0,0,0,0,0".format(vardef.name))  # @todo store float value in 5 byte format
                        else:
                            raise TypeError("weird datatype")
                elif vardef.type in (DataType.BYTEARRAY, DataType.WORDARRAY):
                    if vardef.address:
                        raise CodeError("array or wordarray vars must not have address; will be allocated by assembler")
                    if vardef.type == DataType.BYTEARRAY:
                        self.p("{:s}\t\t.fill {:d}, ${:02x}".format(vardef.name, vardef.length, vardef.value or 0))
                    elif vardef.type == DataType.WORDARRAY:
                        f_hi, f_lo = divmod(vardef.value or 0, 256)  # type: ignore
                        self.p("{:s}\t\t.fill {:d}, [${:02x}, ${:02x}]\t; {:d} words of ${:04x}"
                               .format(vardef.name, vardef.length * 2, f_lo, f_hi, vardef.length, vardef.value or 0))
                    else:
                        raise TypeError("invalid vartype", vardef.type)
                elif vardef.type == DataType.MATRIX:
                    if vardef.address:
                        raise CodeError("matrix vars must not have address; will be allocated by assembler")
                    self.p("{:s}\t\t.fill {:d}, ${:02x}\t\t; matrix {:d}*{:d} bytes"
                           .format(vardef.name,
                                   vardef.matrixsize[0] * vardef.matrixsize[1],
                                   vardef.value or 0,
                                   vardef.matrixsize[0], vardef.matrixsize[1]))
                elif vardef.type == DataType.STRING:
                    # 0-terminated string
                    self.p("{:s}\n\t\t.null {:s}".format(vardef.name, self.output_string(str(vardef.value))))
                elif vardef.type == DataType.STRING_P:
                    # pascal string
                    self.p("{:s}\n\t\t.ptext {:s}".format(vardef.name, self.output_string(str(vardef.value))))
                elif vardef.type == DataType.STRING_S:
                    # 0-terminated string in screencode encoding
                    self.p(".enc 'screen'")
                    self.p("{:s}\n\t\t.null {:s}".format(vardef.name, self.output_string(str(vardef.value), True)))
                    self.p(".enc 'none'")
                elif vardef.type == DataType.STRING_PS:
                    # 0-terminated pascal string in screencode encoding
                    self.p(".enc 'screen'")
                    self.p("{:s}\n\t\t.ptext {:s}".format(vardef.name, self.output_string(str(vardef.value), True)))
                    self.p(".enc 'none'")
                else:
                    raise CodeError("unknown variable type " + str(vardef.type))

    def generate_statement(self, stmt: ParseResult._Stmt) -> None:
        if isinstance(stmt, ParseResult.ReturnStmt):
            if stmt.a:
                if isinstance(stmt.a, ParseResult.IntegerValue):
                    self.p("\t\tlda #{:d}".format(stmt.a.value))
                else:
                    raise CodeError("can only return immediate values for now")  # XXX
            if stmt.x:
                if isinstance(stmt.x, ParseResult.IntegerValue):
                    self.p("\t\tldx #{:d}".format(stmt.x.value))
                else:
                    raise CodeError("can only return immediate values for now")  # XXX
            if stmt.y:
                if isinstance(stmt.y, ParseResult.IntegerValue):
                    self.p("\t\tldy #{:d}".format(stmt.y.value))
                else:
                    raise CodeError("can only return immediate values for now")  # XXX
            self.p("\t\trts")
        elif isinstance(stmt, ParseResult.AssignmentStmt):
            if not self.previous_stmt_was_assignment:
                # if the previous statement was not assignment, clear the reg values and assume nothing
                # otherwise, the previous values continue to be used
                self.reg_values = {'A': None, 'X': None, 'Y': None}
            self.generate_assignment(stmt)
        elif isinstance(stmt, ParseResult.Label):
            self.p("\n{:s}\t\t\t\t; src l. {:d}".format(stmt.name, stmt.linenum))
        elif isinstance(stmt, ParseResult.IncrDecrStmt):
            if stmt.howmuch in (-1, 1):
                if isinstance(stmt.what, ParseResult.RegisterValue):
                    if stmt.howmuch == 1:
                        if stmt.what.register == 'A':
                            self.p("\t\tadc #1")
                        else:
                            self.p("\t\tin{:s}".format(stmt.what.register.lower()))
                    else:
                        if stmt.what.register == 'A':
                            self.p("\t\tsbc #1")
                        else:
                            self.p("\t\tde{:s}".format(stmt.what.register.lower()))
                elif isinstance(stmt.what, ParseResult.MemMappedValue):
                    r_str = stmt.what.name or self.to_hex(stmt.what.address)
                    if stmt.what.datatype == DataType.BYTE:
                        if stmt.howmuch == 1:
                            self.p("\t\tinc " + r_str)
                        else:
                            self.p("\t\tdec " + r_str)
                    elif stmt.what.datatype == DataType.WORD:
                        # @todo verify this asm code
                        if stmt.howmuch == 1:
                            self.p("\t\tinc " + r_str)
                            self.p("\t\tbne  +")
                            self.p("\t\tinc {:s}+1".format(r_str))
                            self.p("+")
                        else:
                            self.p("\t\tdec " + r_str)
                            self.p("\t\tbne  +")
                            self.p("\t\tdec {:s}+1".format(r_str))
                            self.p("+")
                    else:
                        raise CodeError("cannot in/decrement memory of type " + str(stmt.what.datatype))
                else:
                    raise CodeError("cannot in/decrement " + str(stmt.what))
            elif stmt.howmuch > 0:
                raise NotImplementedError("incr by > 1")  # XXX
            elif stmt.howmuch < 0:
                raise NotImplementedError("decr by > 1")  # XXX
        elif isinstance(stmt, ParseResult.CallStmt):
            if stmt.call_label:
                call_target = stmt.call_label
                if stmt.call_module:
                    call_target = stmt.call_module + "." + stmt.call_label
            else:
                call_target = self.to_hex(stmt.address)
            if stmt.subroutine:
                if stmt.subroutine.clobbered_registers:
                    with self.save_registers_for_subroutine_call(stmt.subroutine.clobbered_registers, stmt.is_goto):
                        self.p("\t\tjsr " + call_target)
                    return
            if stmt.is_goto:
                self.p("\t\tjmp " + call_target)
            else:
                self.p("\t\tjsr " + call_target)
        elif isinstance(stmt, ParseResult.InlineAsm):
            self.p("\t\t; inline asm, src l. {:d}".format(stmt.linenum))
            for line in stmt.asmlines:
                self.p(line)
            self.p("\t\t; end inline asm, src l. {:d}".format(stmt.linenum))
        else:
            raise CodeError("unknown statement " + repr(stmt))
        self.previous_stmt_was_assignment = isinstance(stmt, ParseResult.AssignmentStmt)

    def generate_assignment(self, stmt: ParseResult.AssignmentStmt) -> None:
        self.p("\t\t\t\t\t; src l. {:d}".format(stmt.linenum))
        if isinstance(stmt.right, ParseResult.IntegerValue):
            r_str = stmt.right.name if stmt.right.name else "${:x}".format(stmt.right.value)
            # @todo optimize below if there are multiple lvalues that require a pha/pla, do it just once and reuse the value
            for lv in stmt.leftvalues:
                if isinstance(lv, ParseResult.RegisterValue):
                    self.generate_assign_const_to_reg(lv.register, r_str, stmt.right.value)
                elif isinstance(lv, ParseResult.MemMappedValue):
                    self.generate_assign_const_to_mem(lv, r_str, stmt.right.value)
                else:
                    raise CodeError("invalid assignment target (1)", str(stmt))
        elif isinstance(stmt.right, ParseResult.RegisterValue):
            for lv in stmt.leftvalues:
                if isinstance(lv, ParseResult.RegisterValue):
                    self.generate_assign_reg_to_reg(lv, stmt.right.register)
                elif isinstance(lv, ParseResult.MemMappedValue):
                    self.generate_assign_reg_to_memory(lv, stmt.right.register)
                else:
                    raise CodeError("invalid assignment target (2)", str(stmt))
        elif isinstance(stmt.right, ParseResult.StringValue):
            r_str = self.output_string(stmt.right.value, True)
            for lv in stmt.leftvalues:
                if isinstance(lv, ParseResult.RegisterValue):
                    if len(stmt.right.value) == 1:
                        self.generate_assign_char_to_reg(lv, r_str)
                    else:
                        self.generate_assign_string_to_reg(lv, stmt.right)
                elif isinstance(lv, ParseResult.MemMappedValue):
                    if len(stmt.right.value) == 1:
                        self.generate_assign_char_to_memory(lv, r_str)
                    else:
                        self.generate_assign_string_to_memory(lv, stmt.right)
                else:
                    raise CodeError("invalid assignment target (2)", str(stmt))
        elif isinstance(stmt.right, ParseResult.MemMappedValue):
            if stmt.right.datatype != DataType.BYTE:
                raise CodeError("can only assign memory mapped byte values for now", str(stmt))  # @todo support other mmapped types
            r_str = stmt.right.name if stmt.right.name else "${:x}".format(stmt.right.address)
            for lv in stmt.leftvalues:
                if isinstance(lv, ParseResult.RegisterValue):
                    self.generate_assign_mem_to_reg(lv.register, r_str)
                elif isinstance(lv, ParseResult.MemMappedValue):
                    if lv.datatype != DataType.BYTE:
                        raise CodeError("can only assign a memory mapped byte value into another byte")
                    self.generate_assign_mem_to_mem(lv, r_str)
                else:
                    raise CodeError("invalid assignment target (4)", str(stmt))
        else:
            raise CodeError("invalid assignment value type", str(stmt))

    def generate_assign_mem_to_reg(self, l_register: str, r_str: str) -> None:
        # Register = memory (byte)
        if l_register in ('A', 'X', 'Y'):
            self.p("\t\tld{:s} {:s}".format(l_register.lower(), r_str))
            self.reg_values[l_register] = None
        else:
            raise CodeError("invalid register for memory byte assignment", l_register, r_str)

    def generate_assign_reg_to_memory(self, lv: ParseResult.MemMappedValue, r_register: str) -> None:
        # Memory = Register
        lv_string = lv.name or self.to_hex(lv.address)
        if lv.datatype == DataType.BYTE:
            self.p("\t\tst{:s} {}".format(r_register.lower(), lv_string))
        elif lv.datatype == DataType.WORD:
            self.p("\t\tst{:s} {}".format(r_register.lower(), lv_string))  # lsb
            # now set the msb to zero
            if self.reg_values['X'] == 0:
                self.p("\t\tstx {}+1".format(lv_string))
            elif self.reg_values['Y'] == 0:
                self.p("\t\tsty {}+1".format(lv_string))
            elif self.reg_values['A'] == 0:
                self.p("\t\tsta {}+1".format(lv_string))
            else:
                self.p("\t\tstx ${0:02x}\n\t\tldx #0\n\t\tstx {1}+1\n\t\tldx ${0:02x}"
                       .format(Zeropage.SCRATCH_B1, lv_string))
        else:
            raise CodeError("invalid lvalue type", lv.datatype)

    def generate_assign_reg_to_reg(self, lv: ParseResult.RegisterValue, r_register: str) -> None:
        # Register = Register
        if lv.register != r_register:
            if lv.register == 'A':  # x/y -> a
                self.p("\t\tt{:s}a".format(r_register.lower()))
                self.reg_values['A'] = self.reg_values[r_register]
            elif lv.register == 'Y':
                if r_register == 'A':
                    # a -> y
                    self.p("\t\ttay")
                    self.reg_values['Y'] = self.reg_values['A']
                else:
                    # x -> y, 6502 doesn't have txy
                    self.p("\t\tstx ${0:02x}\n\t\tldy ${0:02x}".format(Zeropage.SCRATCH_B1))
                    self.reg_values['Y'] = self.reg_values['X']
            elif lv.register == 'X':
                if r_register == 'A':
                    # a -> x
                    self.p("\t\ttax")
                    self.reg_values['X'] = self.reg_values['A']
                else:
                    # y -> x, 6502 doesn't have tyx
                    self.p("\t\tsty ${0:02x}\n\t\tldx ${0:02x}".format(Zeropage.SCRATCH_B1))
                    self.reg_values['X'] = self.reg_values['Y']
            elif lv.register in REGISTER_WORDS:
                if len(r_register) == 1:
                    raise CodeError("need register pair to assign to other register pair")
                if lv.register == "AX" and r_register == "AY":
                    # y -> x, 6502 doesn't have tyx
                    self.p("\t\tsty ${0:02x}\n\t\tldx ${0:02x}".format(Zeropage.SCRATCH_B1))
                    self.reg_values['X'] = self.reg_values['Y']
                elif lv.register == "AX" and r_register == "XY":
                    self.p("\t\ttxa")
                    # y -> x, 6502 doesn't have tyx
                    self.p("\t\tsty ${0:02x}\n\t\tldx ${0:02x}".format(Zeropage.SCRATCH_B1))
                    self.reg_values['A'] = self.reg_values['X']
                    self.reg_values['X'] = self.reg_values['Y']
                elif lv.register == "AY" and r_register == "AX":
                    # x -> y, 6502 doesn't have txy
                    self.p("\t\tstx ${0:02x}\n\t\tldy ${0:02x}".format(Zeropage.SCRATCH_B1))
                    self.reg_values['Y'] = self.reg_values['X']
                elif lv.register == "AY" and r_register == "XY":
                    self.p("\t\ttxa")
                    self.reg_values['A'] = self.reg_values['X']
                elif lv.register == "XY" and r_register == "AX":
                    self.p("\t\ttax")
                    # x -> y, 6502 doesn't have txy
                    self.p("\t\tstx ${0:02x}\n\t\tldy ${0:02x}".format(Zeropage.SCRATCH_B1))
                    self.reg_values['X'] = self.reg_values['A']
                    self.reg_values['Y'] = self.reg_values['X']
                elif lv.register == "XY" and r_register == "AY":
                    self.p("\t\ttax")
                    self.reg_values['X'] = self.reg_values['A']
                else:
                    raise CodeError("invalid register combination", lv.register, r_register)
            else:
                raise CodeError("invalid register " + lv.register)

    @contextlib.contextmanager
    def save_a_reg_for_assignment(self, value_being_set: Union[int, str]):
        # only use this for assignment statement generation
        if value_being_set is None or self.reg_values['A'] != value_being_set:
            self.p("\t\tpha")
            save_a_value = self.reg_values['A']
            yield
            self.p("\t\tpla")
            self.reg_values['A'] = save_a_value
        else:
            yield

    @contextlib.contextmanager
    def save_registers_for_subroutine_call(self, registers: Set[str], is_goto: bool):
        if 'A' in registers:
            self.p("\t\tpha")
        if 'X' in registers:
            self.p("\t\ttxa\n\t\tpha")
        if 'Y' in registers:
            self.p("\t\ttya\n\t\tpha")
        yield
        if 'Y' in registers:
            self.p("\t\tpla\n\t\ttay")
        if 'X' in registers:
            self.p("\t\tpla\n\t\ttax")
        if 'A' in registers:
            self.p("\t\tpla")
        if is_goto:
            self.p("\t\trts")

    def generate_assign_const_to_mem(self, lv: ParseResult.MemMappedValue, const_str: str, const_value: int) -> None:
        # Memory = Constant
        with self.save_a_reg_for_assignment(const_value):
            if not lv.name:
                # assign a single byte value to a memory location
                if not DataType.BYTE.assignable_from_value(const_value):
                    raise OverflowError("const value doesn't fit in a byte")
                if self.reg_values['A'] != const_value:
                    self.p("\t\tlda #" + const_str)
                    self.reg_values['A'] = const_value
                self.p("\t\tsta " + self.to_hex(lv.address))
                return
            # assign constant value to a memory location by symbol name
            symblock, sym = self.parsed.lookup_symbol(lv.name, self.cur_block)
            if isinstance(sym, VariableDef):
                assign_target = lv.name
                if symblock is not self.cur_block:
                    assign_target = symblock.label + "." + sym.name
                if sym.type == DataType.BYTE:
                    if not DataType.BYTE.assignable_from_value(const_value):
                        raise OverflowError("const value doesn't fit in a byte")
                    if self.reg_values['A'] != const_value:
                        self.p("\t\tlda #" + const_str)
                        self.reg_values['A'] = const_value
                    self.p("\t\tsta " + assign_target)
                elif sym.type == DataType.WORD:
                    p1 = "\t\tlda #<" + const_str
                    p2 = "\t\tlda #>" + const_str
                    self.p(p1)
                    self.p("\t\tsta " + assign_target)
                    self.p(p2)
                    self.reg_values['A'] = const_value
                    self.p("\t\tsta {}+1".format(assign_target))
                else:
                    raise TypeError("invalid lvalue type " + str(sym))
            else:
                raise TypeError("invalid lvalue type " + str(sym))

    def generate_assign_mem_to_mem(self, lv: ParseResult.MemMappedValue, r_str: str) -> None:
        # Address/Memory = Memory (byte)
        with self.save_a_reg_for_assignment(None):
            self.p("\t\tlda " + r_str)
            self.reg_values['A'] = None
            self.p("\t\tsta " + (lv.name or self.to_hex(lv.address)))

    def generate_assign_char_to_memory(self, lv: ParseResult.MemMappedValue, char_str: str) -> None:
        # Memory = Character
        with self.save_a_reg_for_assignment(char_str):
            if self.reg_values['A'] != char_str:
                self.p("\t\tlda #" + char_str)
                self.reg_values['A'] = char_str
            if not lv.name:
                self.p("\t\tsta " + self.to_hex(lv.address))
                return
            # assign char value to a memory location by symbol name
            symblock, sym = self.parsed.lookup_symbol(lv.name, self.cur_block)
            if isinstance(sym, VariableDef):
                assign_target = lv.name
                if symblock is not self.cur_block:
                    assign_target = symblock.label + "." + sym.name
                if sym.type == DataType.BYTE:
                    self.p("\t\tsta " + assign_target)
                elif sym.type == DataType.WORD:
                    self.p("\t\tsta " + assign_target)
                    self.p("\t\tlda #0")
                    self.reg_values['A'] = 0
                    self.p("\t\tsta {}+1".format(assign_target))
                else:
                    raise TypeError("invalid lvalue type " + str(sym))
            else:
                raise TypeError("invalid lvalue type " + str(sym))

    def generate_assign_const_to_reg(self, l_register: str, r_str: str, r_value: int) -> None:
        # Register = Constant
        if l_register in ('A', 'X', 'Y'):
            if self.reg_values[l_register] != r_value:
                # optimize to txa/tax/tya/tay if possible
                if l_register == 'A' and self.reg_values['X'] == r_value:
                    self.p("\t\ttxa")
                elif l_register == 'A' and self.reg_values['Y'] == r_value:
                    self.p("\t\ttya")
                elif l_register == 'X' and self.reg_values['A'] == r_value:
                    self.p("\t\ttax")
                elif l_register == 'Y' and self.reg_values['A'] == r_value:
                    self.p("\t\ttay")
                else:
                    self.p("\t\tld{:s} #{:s}".format(l_register.lower(), r_str))
                self.reg_values[l_register] = r_value
        elif l_register == "SC":
            # set/clear S carry bit
            if r_value:
                self.p("\t\tsec")
            else:
                self.p("\t\tclc")
        elif l_register in REGISTER_WORDS:
            high, low = divmod(r_value, 256)
            self.generate_assign_const_to_reg(l_register[0], "<" + r_str, low)
            self.generate_assign_const_to_reg(l_register[1], ">" + r_str, high)
        else:
            raise CodeError("invalid register in const assignment", l_register, r_value)

    def generate_assign_char_to_reg(self, lv: ParseResult.RegisterValue, char_str: str) -> None:
        # Register = Char (string of length 1)
        if lv.register not in ('A', 'X', 'Y'):
            raise CodeError("invalid register for char assignment", lv.register)
        if (lv.register == 'A' and self.reg_values['A'] != char_str) or \
                (lv.register in ('X', 'Y') and self.reg_values[lv.register] != char_str):
            self.p("\t\tld{:s} #{:s}".format(lv.register.lower(), char_str))
            self.reg_values[lv.register] = char_str

    def generate_assign_string_to_reg(self, lv: ParseResult.RegisterValue, rvalue: ParseResult.StringValue) -> None:
        if lv.register not in ("AX", "AY", "XY"):
            raise CodeError("need register pair AX, AY or XY for string address assignment", lv.register)
        if rvalue.name:
            self.p("\t\tld{:s} #<{:s}".format(lv.register[0].lower(), rvalue.name))
            self.p("\t\tld{:s} #>{:s}".format(lv.register[1].lower(), rvalue.name))
            self.reg_values[lv.register[0]] = None
            self.reg_values[lv.register[1]] = None
        else:
            raise CodeError("cannot assign immediate string, it should be a string variable")

    def generate_assign_string_to_memory(self, lv: ParseResult.MemMappedValue, rvalue: ParseResult.StringValue) -> None:
        if lv.datatype != DataType.WORD:
            raise CodeError("need word memory type for string address assignment")
        if rvalue.name:
            self.p("\t\tlda #<{:s}".format(rvalue.name))
            self.p("\t\tsta " + self.to_hex(lv.address))
            self.p("\t\tlda #>{:s}".format(rvalue.name))
            self.p("\t\tsta " + self.to_hex(lv.address+1))
            self.reg_values["A"] = None
        else:
            raise CodeError("cannot assign immediate string, it should be a string variable")

    def footer(self) -> None:
        self.p("\n\n.end")

    def output_string(self, value: str, screencodes: bool = False) -> str:
        if len(value) == 1 and screencodes:
            if value[0].isprintable() and ord(value[0]) < 128:
                return "'{:s}'".format(value[0])
            else:
                return str(ord(value[0]))
        result = '"'
        for char in value:
            if char in "{}":
                result += '", {:d}, "'.format(ord(char))
            elif char.isprintable() and ord(char) < 128:
                result += char
            else:
                if screencodes:
                    result += '", {:d}, "'.format(ord(char))
                else:
                    if char == "\f":
                        result += "{clear}"
                    elif char == "\b":
                        result += "{delete}"
                    elif char == "\n":
                        result += "{lf}"
                    elif char == "\r":
                        result += "{cr}"
                    elif char == "\t":
                        result += "{tab}"
                    else:
                        result += '", {:d}, "'.format(ord(char))
        return result + '"'


class Assembler64Tass:
    def __init__(self, format: ProgramFormat) -> None:
        self.format = format

    def assemble(self, inputfilename: str, outputfilename: str) -> None:
        args = ["64tass", "--ascii", "--case-sensitive", "-Wall", "-Wno-strict-bool", "--dump-labels",
                "--labels", outputfilename+".labels.txt", "--output", outputfilename, inputfilename]
        if self.format == ProgramFormat.PRG:
            args.append("--cbm-prg")
        elif self.format == ProgramFormat.RAW:
            args.append("--nostart")
        else:
            raise ValueError("don't know how to create format "+str(self.format))
        try:
            if self.format == ProgramFormat.PRG:
                print("\ncreating C-64 .prg...\n")
            elif self.format == ProgramFormat.RAW:
                print("\ncreating raw binary...\n")
            subprocess.check_call(args)
        except subprocess.CalledProcessError as x:
            print("assembler failed with returncode", x.returncode)


def main() -> None:
    ap = argparse.ArgumentParser(description="Compiler for IL65 language")
    ap.add_argument("-o", "--output", help="output directory")
    ap.add_argument("sourcefile", help="the source .ill/.il65 file to compile")
    args = ap.parse_args()
    assembly_filename = os.path.splitext(args.sourcefile)[0] + ".asm"
    program_filename = os.path.splitext(args.sourcefile)[0] + ".prg"
    if args.output:
        os.makedirs(args.output, mode=0o700, exist_ok=True)
        assembly_filename = os.path.join(args.output, os.path.split(assembly_filename)[1])
        program_filename = os.path.join(args.output, os.path.split(program_filename)[1])

    p = Parser(args.sourcefile, args.output)
    parsed = p.parse()
    if parsed:
        opt = Optimizer(parsed)
        parsed = opt.optimize()
        cg = CodeGenerator(parsed)
        cg.generate()
        cg.optimize()
        with open(assembly_filename, "wt") as out:
            cg.write_assembly(out)
        assembler = Assembler64Tass(parsed.format)
        assembler.assemble(assembly_filename, program_filename)


if __name__ == "__main__":
    main()
