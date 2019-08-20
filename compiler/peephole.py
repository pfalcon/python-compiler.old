from dis import EXTENDED_ARG, opmap, opname
import opcode
from types import CodeType
from typing import Tuple
from typing import Generator

NOP = opmap["NOP"]

BINARY_ADD = opmap["BINARY_ADD"]
BINARY_AND = opmap["BINARY_AND"]
BINARY_FLOOR_DIVIDE = opmap["BINARY_FLOOR_DIVIDE"]
BINARY_LSHIFT = opmap["BINARY_LSHIFT"]
BINARY_MODULO = opmap["BINARY_MODULO"]
BINARY_MULTIPLY = opmap["BINARY_MULTIPLY"]
BINARY_OR = opmap["BINARY_OR"]
BINARY_POWER = opmap["BINARY_POWER"]
BINARY_RSHIFT = opmap["BINARY_RSHIFT"]
BINARY_SUBSCR = opmap["BINARY_SUBSCR"]
BINARY_SUBTRACT = opmap["BINARY_SUBTRACT"]
BINARY_TRUE_DIVIDE = opmap["BINARY_TRUE_DIVIDE"]
BINARY_XOR = opmap["BINARY_XOR"]

COMPARE_OP = opmap["COMPARE_OP"]
LOAD_CONST = opmap["LOAD_CONST"]
RETURN_VALUE = opmap["RETURN_VALUE"]
UNARY_INVERT = opmap["UNARY_INVERT"]
UNARY_NEGATIVE = opmap["UNARY_NEGATIVE"]
UNARY_NOT = opmap["UNARY_NOT"]
UNARY_POSITIVE = opmap["UNARY_POSITIVE"]

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


UNARY_OPS = {
    UNARY_INVERT: lambda v: ~v,
    UNARY_NEGATIVE: lambda v: -v,
    UNARY_POSITIVE: lambda v: +v,
}

MAX_INT_SIZE = 128
MAX_COLLECTION_SIZE = 20
MAX_STR_SIZE = 20
MAX_TOTAL_ITEMS = 1024


def check_complexity(obj, limit):
    if isinstance(obj, (frozenset, tuple)):
        limit -= len(obj)
        for item in obj:
            limit = check_complexity(item, limit)
            if limit < 0:
                break

    return limit


def safe_multiply(l, r):
    if isinstance(l, int) and isinstance(r, int) and l and r:
        lbits = l.bit_length()
        rbits = r.bit_length()
        if lbits + rbits > MAX_INT_SIZE:
            raise OverflowError()
    elif isinstance(l, int) and isinstance(r, (tuple, frozenset)):
        rsize = len(r)
        if rsize:
            if l < 0 or l > MAX_COLLECTION_SIZE / rsize:
                raise OverflowError()
            if l:
                if check_complexity(r, MAX_TOTAL_ITEMS / l) < 0:
                    raise OverflowError()
    elif isinstance(l, int) and isinstance(r, (str, bytes)):
        rsize = len(r)
        if rsize:
            if l < 0 or l > MAX_STR_SIZE / rsize:
                raise OverflowError()
    elif isinstance(r, int) and isinstance(l, (tuple, frozenset, str, bytes)):
        return safe_multiply(r, l)

    return l * r


def safe_power(l, r):
    if isinstance(l, int) and isinstance(r, int) and l and r > 0:
        lbits = l.bit_length()
        if lbits > MAX_INT_SIZE / r:
            raise OverflowError()

    return l ** r


def safe_mod(l, r):
    if isinstance(l, (str, bytes)):
        raise OverflowError()

    return l % r


def safe_lshift(l, r):
    if isinstance(l, int) and isinstance(r, int) and l and r:
        lbits = l.bit_length()
        if r < 0 or r > MAX_INT_SIZE or lbits > MAX_INT_SIZE - r:
            raise OverflowError()

    return l << r


BINARY_OPS = {
    BINARY_POWER: safe_power,
    BINARY_MULTIPLY: safe_multiply,
    BINARY_TRUE_DIVIDE: lambda l, r: l / r,
    BINARY_FLOOR_DIVIDE: lambda l, r: l // r,
    BINARY_MODULO: safe_mod,
    BINARY_ADD: lambda l, r: l + r,
    BINARY_SUBTRACT: lambda l, r: l - r,
    BINARY_SUBSCR: lambda l, r: l[r],
    BINARY_LSHIFT: safe_lshift,
    BINARY_RSHIFT: lambda l, r: l >> r,
    BINARY_AND: lambda l, r: l & r,
    BINARY_XOR: lambda l, r: l ^ r,
    BINARY_OR: lambda l, r: l | r,
}


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
        self.consts = list(code.co_consts)
        self.codestr = bytearray(code.co_code)
        self.blocks = self.markblocks()
        self.const_stack = []
        self.in_consts = False

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

    def push_const(self, const):
        self.const_stack.append(const)
        self.in_consts = True

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

            if not self.in_consts:
                del self.const_stack[:]
            self.in_consts = False

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

    @ophandler(LOAD_CONST)
    def opt_load_const(self, i, opcode, op_start, nextop, nexti):
        # Skip over LOAD_CONST trueconst
        # POP_JUMP_IF_FALSE xx.  This improves
        # "while 1" performance.
        # The above comment is from CPython.  This optimization is now performed
        # at the AST level and is also applied to if statements.  But it does
        # not get applied to conditionals, e.g. 1 if 2 else 3
        self.push_const(self.consts[get_arg(self.codestr, i)])
        if (
            nextop != POP_JUMP_IF_FALSE
            or not self.is_basic_block(op_start, i + 1)
            or not bool(self.consts[get_arg(self.codestr, i)])
        ):
            return
        self.fill_nops(op_start, nexti + 1)

    @ophandler(RETURN_VALUE)
    def opt_return_value(self, i, opcode, op_start, nextop, nexti):
        h = i + 1
        block_id = self.blocks[i]
        while h < len(self.codestr) // 2 and self.blocks[h] == block_id:
            h += 1

        if h > i + 1:
            self.fill_nops(i + 1, h)
            nexti = self.find_op(h)

    @ophandler(*UNARY_OPS)
    def op_unary_constants(self, i, opcode, op_start, nextop, nexti):
        # Fold unary ops on constants.
        #  LOAD_CONST c1  UNARY_OP --> LOAD_CONST unary_op(c)
        if not self.const_stack:
            return
        h = self.lastn_const_start(op_start, 1)
        if self.is_basic_block(h, op_start):
            h = self.fold_unaryops_on_constants(h, i + 1, opcode)
            if h >= 0:
                self.const_stack[-1] = self.consts[get_arg(self.codestr, i)]
                self.in_consts = True

    @ophandler(*BINARY_OPS)
    def op_binary_constants(self, i, opcode, op_start, nextop, nexti):
        if len(self.const_stack) < 2:
            return
        h = self.lastn_const_start(op_start, 2)
        if self.is_basic_block(h, op_start):
            h = self.fold_binops_on_constants(h, i + 1, opcode)
            if h >= 0:
                del self.const_stack[-1]
                self.const_stack[-1] = self.consts[get_arg(self.codestr, i)]
                self.in_consts = True

    def fold_binops_on_constants(self, c_start, opcode_end, opcode):
        l = self.const_stack[-2]
        r = self.const_stack[-1]
        try:
            v = BINARY_OPS[opcode](l, r)
        except Exception:
            return -1

        # CPython does nothing to optimize these, and doing something like
        # -+-+-+-+-+-+-+-+42  just bloats the constant table with unused entries
        self.consts.append(v)

        return self.copy_op_arg(c_start, LOAD_CONST, len(self.consts) - 1, opcode_end)

    def fold_unaryops_on_constants(self, c_start, opcode_end, opcode):
        v = self.const_stack[-1]
        try:
            v = UNARY_OPS[opcode](v)
        except TypeError:
            return -1

        # CPython does nothing to optimize these, and doing something like
        # -+-+-+-+-+-+-+-+42  just bloats the constant table with unused entries
        self.consts.append(v)

        return self.copy_op_arg(c_start, LOAD_CONST, len(self.consts) - 1, opcode_end)

    def copy_op_arg(self, i, op, oparg, maxi):
        ilen = instrsize(oparg)
        if ilen + i > maxi:
            return -1
        self.write_op_arg(maxi - ilen, op, oparg, ilen)
        self.fill_nops(i, maxi - ilen)
        return maxi - 1

    def lastn_const_start(self, i, n):
        assert n > 0
        while True:
            i -= 1
            assert i >= 0
            opcode = self.codestr[i * 2]
            if opcode == LOAD_CONST:
                n -= 1
                if not n:
                    while i > 0 and self.codestr[i * 2 - 2] == EXTENDED_ARG:
                        i -= 1
                    return i
            else:
                assert opcode == NOP or opcode == EXTENDED_ARG

    def make_new_code(self, codestr, lnotab):
        return CodeType(
            self.code.co_argcount,
            self.code.co_kwonlyargcount,
            self.code.co_nlocals,
            self.code.co_stacksize,
            self.code.co_flags,
            bytes(codestr),
            tuple(self.consts),
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
