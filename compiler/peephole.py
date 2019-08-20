from dis import EXTENDED_ARG, opmap, opname
import opcode
from types import CodeType
from typing import Tuple
from typing import Generator

NOP = opmap["NOP"]

COMPARE_OP = opmap["COMPARE_OP"]
UNARY_NOT = opmap["UNARY_NOT"]

CONTINUE_LOOP = opmap["CONTINUE_LOOP"]
JUMP_ABSOLUTE = opmap["JUMP_ABSOLUTE"]
JUMP_IF_FALSE_OR_POP = opmap["JUMP_IF_FALSE_OR_POP"]
JUMP_IF_TRUE_OR_POP = opmap["JUMP_IF_TRUE_OR_POP"]
POP_JUMP_IF_FALSE = opmap["POP_JUMP_IF_FALSE"]
POP_JUMP_IF_TRUE = opmap["POP_JUMP_IF_TRUE"]

FOR_ITER = opmap["FOR_ITER"]
JUMP_FORWARD = opmap["JUMP_FORWARD"]
SETUP_ASYNC_WITH = opmap["SETUP_ASYNC_WITH"]
SETUP_EXCEPT = opmap["SETUP_EXCEPT"]
SETUP_FINALLY = opmap["SETUP_FINALLY"]
SETUP_LOOP = opmap["SETUP_LOOP"]
SETUP_WITH = opmap["SETUP_WITH"]

ABS_JUMPS = set(opcode.hasjabs)
REL_JUMPS = set(opcode.hasjrel)


CMP_OP_IN = opcode.cmp_op.index('in')
CMP_OP_IS_NOT = opcode.cmp_op.index('is not')

assert CMP_OP_IN < CMP_OP_IS_NOT
assert opcode.cmp_op.index('not in') > CMP_OP_IN and opcode.cmp_op.index('not in') < CMP_OP_IS_NOT
assert opcode.cmp_op.index('is') > CMP_OP_IN and opcode.cmp_op.index('is') < CMP_OP_IS_NOT

assert (CMP_OP_IS_NOT - CMP_OP_IN) == 3


def get_op(code, i):
    return code[i * 2]


def get_arg(code, i):
    index = i * 2 + 1
    oparg = code[index]
    if i >= 1 and get_op(code, i - 1) == EXTENDED_ARG:
        oparg |= code[index - 2] << 8
        if i >= 2 and get_op(code, i - 2) == EXTENDED_ARG:
            oparg |= code[index - 4] << 16
            if i >= 3 and get_op(code, i - 3) == EXTENDED_ARG:
                oparg |= code[index - 6] << 24
    return oparg


def cast_signed_byte_to_unsigned(i):
    if i < 0:
        i = 255 + i + 1
    return i


def instrsize(oparg):
    if oparg <= 0xFF:
        return 1
    elif oparg <= 0xFFFF:
        return 2
    elif oparg <= 0xFFFFFF:
        return 3

    assert oparg <= 0xFFFFFFFF
    return 4


def ophandler_registry():
    registry = {}

    def register(*opcodes):
        def handler(f):
            for opcode in opcodes:
                registry[opcode] = f
            return f

        return handler

    return registry, register


class Optimizer:
    def __init__(self, code: CodeType) -> None:
        assert len(code.co_code) % 2 == 0
        self.code = code
        self.codestr = bytearray(code.co_code)
        self.blocks = self.markblocks()

    def is_basic_block(self, start, end):
        return self.blocks[start] == self.blocks[end]

    def fill_nops(self, start, end):
        for i in range(start, end):
            self.codestr[i * 2] = NOP

    def find_op(self, i=0):
        for i in range(i, len(self.codestr) // 2):
            if self.codestr[i * 2] != EXTENDED_ARG:
                break
        return i

    def optimize(self) -> CodeType:
        if 0xFF in self.code.co_lnotab:
            # lnotab is too complicated, bail
            return self.code

        i = self.find_op()
        num_operations = len(self.codestr) // 2

        while i < num_operations:
            opcode = self.codestr[i * 2]

            op_start = i
            while op_start >= 1 and self.codestr[(op_start - 1) * 2] == EXTENDED_ARG:
                op_start -= 1
            nexti = i + 1
            while nexti < num_operations and self.codestr[nexti * 2] == EXTENDED_ARG:
                nexti += 1

            nextop = self.codestr[nexti * 2] if nexti < num_operations else 0

            handler = Optimizer.OP_HANDLERS.get(opcode)
            if handler is not None:
                i = handler(self, i, opcode, op_start, nextop, nexti) or nexti
            else:
                i = nexti

        self.fix_blocks()
        lnotab = self.fix_lnotab()
        codestr = self.fix_jumps()
        if codestr is None:
            return self.code

        return self.make_new_code(codestr, lnotab)

    OP_HANDLERS, ophandler = ophandler_registry()

    @ophandler(UNARY_NOT)
    def opt_unary_not(self, i, opcode, op_start, nextop, nexti):
        # Replace UNARY_NOT POP_JUMP_IF_FALSE
        #   with    POP_JUMP_IF_TRUE
        if nextop != POP_JUMP_IF_FALSE or not self.is_basic_block(op_start, i + 1):
            return

        self.fill_nops(op_start, i + 1)
        self.codestr[nexti * 2] = POP_JUMP_IF_TRUE

    @ophandler(COMPARE_OP)
    def opt_compare_op(self, i, opcode, op_start, nextop, nexti):
        # not a is b -->  a is not b
        # not a in b -->  a not in b
        # not a is not b -->  a is b
        # not a not in b -->  a in b
        j = get_arg(self.codestr, i)
        if (
            j < CMP_OP_IN
            or j > CMP_OP_IS_NOT
            or nextop != UNARY_NOT
            or not self.is_basic_block(op_start, i + 1)
        ):
            return

        self.codestr[i * 2 + 1] = j ^ 1
        self.fill_nops(i + 1, nexti + 1)

    def make_new_code(self, codestr, lnotab):
        return CodeType(
            self.code.co_argcount,
            self.code.co_kwonlyargcount,
            self.code.co_nlocals,
            self.code.co_stacksize,
            self.code.co_flags,
            bytes(codestr),
            self.code.co_consts,
            self.code.co_names,
            self.code.co_varnames,
            self.code.co_filename,
            self.code.co_name,
            self.code.co_firstlineno,
            bytes(lnotab),
            self.code.co_freevars,
            self.code.co_cellvars,
        )

    def markblocks(self):
        num_operations = len(self.codestr) // 2
        blocks = [0] * num_operations
        code = self.codestr

        for i in range(num_operations):
            opcode = get_op(code, i)
            if opcode in ABS_JUMPS:
                oparg = get_arg(code, i)
                blocks[oparg // 2] = 1
            elif opcode in REL_JUMPS:
                oparg = get_arg(code, i)
                blocks[oparg // 2 + i + 1] = 1

        blockcnt = 0
        for block in range(num_operations):
            blockcnt += blocks[block]
            blocks[block] = blockcnt

        return blocks

    def fix_blocks(self):
        """updates self.blocks to contain the the new instruction offset for
        each corresponding old instruction"""
        nops = 0
        for i in range(len(self.codestr) // 2):
            # original code offset => new code offset
            self.blocks[i] = i - nops
            if self.codestr[i * 2] == NOP:
                nops += 1

    def fix_lnotab(self):
        lnotab = bytearray(self.code.co_lnotab)
        tabsiz = len(lnotab)
        cum_orig_offset = 0
        last_offset = 0
        for i in range(0, tabsiz, 2):
            cum_orig_offset += lnotab[i]
            assert cum_orig_offset % 2 == 0
            new_offset = self.blocks[cum_orig_offset // 2] * 2
            offset_delta = new_offset - last_offset
            assert offset_delta <= 255
            lnotab[i] = cast_signed_byte_to_unsigned(offset_delta)
            last_offset = new_offset
        return lnotab

    def write_op_arg(self, i, opcode, oparg, size):
        codestr = self.codestr
        ofs = i * 2
        if size == 4:
            codestr[ofs] = EXTENDED_ARG
            codestr[ofs + 1] = (oparg >> 24) & 0xFF
            ofs += 2
        if size >= 3:
            codestr[ofs] = EXTENDED_ARG
            codestr[ofs + 1] = (oparg >> 16) & 0xFF
            ofs += 2
        if size >= 2:
            codestr[ofs] = EXTENDED_ARG
            codestr[ofs + 1] = (oparg >> 8) & 0xFF
            ofs += 2

        codestr[ofs] = opcode
        codestr[ofs + 1] = oparg & 0xFF

    def fix_jumps(self):
        op_start = i = h = 0
        codestr = self.codestr
        blocks = self.blocks
        while i < len(codestr) // 2:
            j = codestr[i * 2 + 1]
            while codestr[i * 2] == EXTENDED_ARG:
                i += 1
                j = j << 8 | codestr[i * 2 + 1]
            opcode = codestr[i * 2]

            if opcode == NOP:
                i += 1
                op_start = i
                continue
            if opcode in ABS_JUMPS:
                j = blocks[j // 2] * 2
            elif opcode in REL_JUMPS:
                j = blocks[j // 2 + i + 1] - blocks[i] - 1
                j *= 2
            nexti = i - op_start + 1

            if instrsize(j) > nexti:
                return None

            # If instrsize(j) < nexti, we'll emit EXTENDED_ARG 0
            self.write_op_arg(h, opcode, j, nexti)

            h += nexti
            i += 1
            op_start = i

        del codestr[h * 2 :]
        return codestr
