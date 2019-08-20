import unittest
from unittest import TestCase
from compiler.peephole import Optimizer
import dis
from dis import opmap, opname
import opcode
from test.bytecode_helper import BytecodeTestCase
from types import CodeType
import compiler.pycodegen
import ast


class PeepHoleTests(BytecodeTestCase):
    def compile(self, code):
        tree = ast.parse(code)
        tree.filename = ""
        gen = compiler.pycodegen.ModuleCodeGenerator(tree, True)
        return gen.getCode()

    def run_code(self, code):
        compiled = self.compile(code)
        d = {}
        exec(compiled, d)
        return d

    def test_unot(self):
        unot = self.run_code(
            """
def unot(x):
    if not x == 2:
        del x"""
        )["unot"]
        self.assertNotInBytecode(unot, "UNARY_NOT")
        self.assertNotInBytecode(unot, "POP_JUMP_IF_FALSE")
        self.assertInBytecode(unot, "POP_JUMP_IF_TRUE")

    def test_elim_inversion_of_is_or_in(self):
        for line, cmp_op in (
            ("not a is b", "is not"),
            ("not a in b", "not in"),
            ("not a is not b", "is"),
            ("not a not in b", "in"),
        ):
            code = self.compile(line)
            self.assertInBytecode(code, "COMPARE_OP", cmp_op)

    def test_unary_op_no_fold_across_block(self):
        code = self.compile("~(- (1 if x else 2))")
        self.assertInBytecode(code, "UNARY_NEGATIVE")
        self.assertInBytecode(code, "UNARY_INVERT")

    def test_unary_op_unfoldable(self):
        lines = [
            "-'abc'",
            "-()",
            "-None",
            "-...",
            "-b''",
        ]
        for line in lines:
            code = self.compile(line)
            self.assertInBytecode(code, "UNARY_NEGATIVE")

    def test_while_one(self):
        # Skip over:  LOAD_CONST trueconst  POP_JUMP_IF_FALSE xx
        f = self.run_code(
            """
def f():
    while 1:
        pass
    return list"""
        )["f"]
        for elem in ("LOAD_CONST", "POP_JUMP_IF_FALSE"):
            self.assertNotInBytecode(f, elem)
        for elem in ("JUMP_ABSOLUTE",):
            self.assertInBytecode(f, elem)

    def make_code(
        self,
        *ops,
        argcount=0,
        kwonlyargcount=0,
        nlocals=0,
        stacksize=0,
        flags=0,
        constants=(),
        names=(),
        varnames=(),
        filename="foo.py",
        name="foo",
        firstlineno=1,
        lnotab=b"",
        freevars=(),
        cellvars=()
    ):
        res = bytearray()
        for op, oparg in ops:
            if oparg >= 256:
                raise NotImplementedError()
            res.append(op)
            res.append(oparg)

        return CodeType(
            argcount,
            kwonlyargcount,
            nlocals,
            stacksize,
            flags,
            bytes(res),
            constants,
            names,
            varnames,
            filename,
            name,
            firstlineno,
            lnotab,
            freevars,
            cellvars,
        )

    def new_code(
        self,
        code,
        argcount=0,
        kwonlyargcount=0,
        nlocals=0,
        stacksize=0,
        flags=0,
        constants=(),
        names=(),
        varnames=(),
        filename="foo.py",
        name="foo",
        firstlineno=1,
        lnotab=b"",
        freevars=(),
        cellvars=(),
    ):
        return CodeType(
            argcount,
            kwonlyargcount,
            nlocals,
            stacksize,
            flags,
            code,
            constants,
            names,
            varnames,
            filename,
            name,
            firstlineno,
            lnotab,
            freevars,
            cellvars,
        )

    def test_mark_blocks_one_block(self):
        code = self.make_code(
            (opmap["LOAD_CONST"], 0), (opmap["RETURN_VALUE"], 0), constants=(None,)
        )
        opt = Optimizer(code)
        self.assertEqual(opt.blocks, [0, 0])

    def test_mark_blocks_one_block(self):
        code = self.make_code(
            (opmap["LOAD_CONST"], 0),
            (opmap["POP_JUMP_IF_TRUE"], 8),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
        )
        opt = Optimizer(code)
        self.assertEqual(opt.blocks, [0, 0, 0, 0, 1, 1])

    def test_mark_blocks_abs_jump_2(self):
        code = self.make_code(
            (opmap["NOP"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["POP_JUMP_IF_TRUE"], 10),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
        )
        opt = Optimizer(code)
        self.assertEqual(opt.blocks, [0, 0, 0, 0, 0, 1, 1])

    def test_mark_blocks_abs_jump(self):
        code = self.make_code(
            (opmap["LOAD_CONST"], 0),
            (opmap["POP_JUMP_IF_TRUE"], 8),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
        )
        opt = Optimizer(code)
        self.assertEqual(opt.blocks, [0, 0, 0, 0, 1, 1])

    def test_mark_blocks_rel_jump(self):
        code = self.make_code(
            (opmap["JUMP_FORWARD"], 6),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
        )
        opt = Optimizer(code)
        self.assertEqual(opt.blocks, [0, 0, 0, 0, 1])

    def test_mark_blocks_rel_jump_2(self):
        code = self.make_code(
            (opmap["NOP"], 0),
            (opmap["JUMP_FORWARD"], 6),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
        )
        opt = Optimizer(code)
        self.assertEqual(opt.blocks, [0, 0, 0, 0, 0, 1])

    def test_fix_blocks(self):
        """fix blocks should update instruction offsets for removed NOPs"""
        code = self.make_code(
            (opmap["NOP"], 0),
            (opmap["JUMP_FORWARD"], 6),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
            lnotab=b"\x01\x01",
        )
        opt = Optimizer(code)
        opt.fix_blocks()
        self.assertEqual(opt.blocks, [0, 0, 1, 2, 3, 4])

    def test_fix_lnotab(self):
        """basic smoke test that fix_lnotab removes NOPs"""
        code = self.make_code(
            (opmap["NOP"], 0),
            (opmap["JUMP_FORWARD"], 6),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
            lnotab=b"\x02\x01",
        )
        opt = Optimizer(code)
        opt.fix_blocks()
        lnotab = bytes(opt.fix_lnotab())

        self.assertEqual(lnotab, b"\x00\x01")

    def test_fix_jump_rel(self):
        """basic smoke test that fix_lnotab removes NOPs"""
        code = self.make_code(
            (opmap["JUMP_FORWARD"], 6),
            (opmap["NOP"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
            lnotab=b"\x02\x01",
        )
        self.assertInBytecode(code, "JUMP_FORWARD", 8)
        opt = Optimizer(code)
        opt.fix_blocks()
        code = self.new_code(bytes(opt.fix_jumps()), constants=(None,))
        self.assertInBytecode(code, "JUMP_FORWARD", 6)

    def test_fix_jump_abs(self):
        """basic smoke test that fix_lnotab removes NOPs"""
        code = self.make_code(
            (opmap["LOAD_CONST"], 0),
            (opmap["POP_JUMP_IF_TRUE"], 10),
            (opmap["NOP"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            constants=(None,),
            lnotab=b"\x02\x01",
        )
        self.assertInBytecode(code, "POP_JUMP_IF_TRUE", 10)
        opt = Optimizer(code)
        opt.fix_blocks()
        code = self.new_code(bytes(opt.fix_jumps()), constants=(None,))
        self.assertInBytecode(code, "POP_JUMP_IF_TRUE", 8)

    def test_fix_jump_drop_extended(self):
        """Handle EXTENDED_ARG removal correctly"""
        ops = [
            (opmap["LOAD_CONST"], 0),
            (opmap["EXTENDED_ARG"], 1),
            (opmap["POP_JUMP_IF_TRUE"], 3),
            *(((opmap["NOP"], 0),) * 256),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
            (opmap["LOAD_CONST"], 0),
            (opmap["RETURN_VALUE"], 0),
        ]
        code = self.make_code(*ops, constants=(None,))
        self.assertInBytecode(code, "POP_JUMP_IF_TRUE", 259)
        opt = Optimizer(code)
        opt.fix_blocks()
        code = self.new_code(bytes(opt.fix_jumps()), constants=(None,))
        self.assertInBytecode(code, "EXTENDED_ARG", 0)
        self.assertInBytecode(code, "POP_JUMP_IF_TRUE", 6)

    def test_load_const_branch(self):
        code = "x = 1 if 1 else 2"
        optcode = self.compile(code)
        self.assertNotInBytecode(optcode, "POP_JUMP_IF_FALSE")

    def test_pack_unpack(self):
        for line, elem in (
            ("a, = a,", "LOAD_CONST"),
            ("a, b = a, b", "ROT_TWO"),
            ("a, b, c = a, b, c", "ROT_THREE"),
        ):
            code = self.compile(line)
            self.assertInBytecode(code, elem)
            self.assertNotInBytecode(code, "BUILD_TUPLE")
            self.assertNotInBytecode(code, "UNPACK_TUPLE")

    def test_folding_of_tuples_of_constants(self):
        for line, elem in (
            ("a = 1,2,3", (1, 2, 3)),
            ('("a","b","c")', ("a", "b", "c")),
            ("a,b,c = 1,2,3", (1, 2, 3)),
            ("(None, 1, None)", (None, 1, None)),
            ("((1, 2), 3, 4)", ((1, 2), 3, 4)),
        ):
            code = self.compile(line)
            self.assertInBytecode(code, "LOAD_CONST", elem)
            self.assertNotInBytecode(code, "BUILD_TUPLE")

        # Long tuples should be folded too.
        code = self.compile(repr(tuple(range(10000))))
        self.assertNotInBytecode(code, "BUILD_TUPLE")
        # One LOAD_CONST for the tuple, one for the None return value
        load_consts = [
            instr
            for instr in dis.get_instructions(code)
            if instr.opname == "LOAD_CONST"
        ]
        self.assertEqual(len(load_consts), 2)

        # Bug 1053819:  Tuple of constants misidentified when presented with:
        # . . . opcode_with_arg 100   unary_opcode   BUILD_TUPLE 1  . . .
        # The following would segfault upon compilation
        def crater():
            (
                ~[
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                    0,
                    1,
                    2,
                    3,
                    4,
                    5,
                    6,
                    7,
                    8,
                    9,
                ],
            )

    def test_folding_of_lists_of_constants(self):
        for line, elem in (
            # in/not in constants with BUILD_LIST should be folded to a tuple:
            ("a in [1,2,3]", (1, 2, 3)),
            ('a not in ["a","b","c"]', ("a", "b", "c")),
            ("a in [None, 1, None]", (None, 1, None)),
            ("a not in [(1, 2), 3, 4]", ((1, 2), 3, 4)),
        ):
            code = self.compile(line)
            self.assertInBytecode(code, "LOAD_CONST", elem)
            self.assertNotInBytecode(code, "BUILD_LIST")

    def test_folding_of_sets_of_constants(self):
        for line, elem in (
            # in/not in constants with BUILD_SET should be folded to a frozenset:
            ("a in {1,2,3}", frozenset({1, 2, 3})),
            ('a not in {"a","b","c"}', frozenset({"a", "c", "b"})),
            ("a in {None, 1, None}", frozenset({1, None})),
            ("a not in {(1, 2), 3, 4}", frozenset({(1, 2), 3, 4})),
            ("a in {1, 2, 3, 3, 2, 1}", frozenset({1, 2, 3})),
        ):
            code = self.compile(line)
            self.assertNotInBytecode(code, "BUILD_SET")
            self.assertInBytecode(code, "LOAD_CONST", elem)

        # Ensure that the resulting code actually works:
        d = self.run_code(
            """
def f(a):
    return a in {1, 2, 3}

def g(a):
    return a not in {1, 2, 3}
"""
        )
        f, g = d["f"], d["g"]
        self.assertTrue(f(3))
        self.assertTrue(not f(4))

        self.assertTrue(not g(3))
        self.assertTrue(g(4))

    def test_folding_of_binops_on_constants(self):
        for line, elem in (
            ("a = 2+3+4", 9),  # chained fold
            ('"@"*4', "@@@@"),  # check string ops
            ('a="abc" + "def"', "abcdef"),  # check string ops
            ("a = 3**4", 81),  # binary power
            ("a = 3*4", 12),  # binary multiply
            ("a = 13//4", 3),  # binary floor divide
            ("a = 14%4", 2),  # binary modulo
            ("a = 2+3", 5),  # binary add
            ("a = 13-4", 9),  # binary subtract
            # ('a = (12,13)[1]', 13),             # binary subscr
            ("a = 13 << 2", 52),  # binary lshift
            ("a = 13 >> 2", 3),  # binary rshift
            ("a = 13 & 7", 5),  # binary and
            ("a = 13 ^ 7", 10),  # binary xor
            ("a = 13 | 7", 15),  # binary or
            ("a = 2 ** -14", 6.103515625e-05),  # binary power neg rhs
        ):
            code = self.compile(line)
            self.assertInBytecode(code, "LOAD_CONST", elem)
            for instr in dis.get_instructions(code):
                self.assertFalse(instr.opname.startswith("BINARY_"))

        # Verify that unfoldables are skipped
        code = self.compile('a=2+"b"')
        self.assertInBytecode(code, "LOAD_CONST", 2)
        self.assertInBytecode(code, "LOAD_CONST", "b")

        # Verify that large sequences do not result from folding
        code = self.compile('a="x"*10000')
        self.assertInBytecode(code, "LOAD_CONST", 10000)
        self.assertNotIn("x" * 10000, code.co_consts)
        code = self.compile("a=1<<1000")
        self.assertInBytecode(code, "LOAD_CONST", 1000)
        self.assertNotIn(1 << 1000, code.co_consts)
        code = self.compile("a=2**1000")
        self.assertInBytecode(code, "LOAD_CONST", 1000)
        self.assertNotIn(2 ** 1000, code.co_consts)

    def test_binary_subscr_on_unicode(self):
        # valid code get optimized
        code = self.compile('"foo"[0]')
        self.assertInBytecode(code, "LOAD_CONST", "f")
        self.assertNotInBytecode(code, "BINARY_SUBSCR")
        code = self.compile('"\u0061\uffff"[1]')
        self.assertInBytecode(code, "LOAD_CONST", "\uffff")
        self.assertNotInBytecode(code, "BINARY_SUBSCR")

        # With PEP 393, non-BMP char get optimized
        code = self.compile('"\U00012345"[0]')
        self.assertInBytecode(code, "LOAD_CONST", "\U00012345")
        self.assertNotInBytecode(code, "BINARY_SUBSCR")

        # invalid code doesn't get optimized
        # out of range
        code = self.compile('"fuu"[10]')
        self.assertInBytecode(code, "BINARY_SUBSCR")

    def test_folding_of_unaryops_on_constants(self):
        for line, elem in (
            ("-0.5", -0.5),  # unary negative
            ("-0.0", -0.0),  # -0.0
            ("-(1.0-1.0)", -0.0),  # -0.0 after folding
            ("-0", 0),  # -0
            ("~-2", 1),  # unary invert
            ("+1", 1),  # unary positive
        ):
            code = self.compile(line)
            self.assertInBytecode(code, "LOAD_CONST", elem)
            for instr in dis.get_instructions(code):
                self.assertFalse(instr.opname.startswith("UNARY_"))

        # Check that -0.0 works after marshaling
        negzero = self.run_code(
            """
def negzero():
    return -(1.0 - 1.0)
"""
        )["negzero"]

        for instr in dis.get_instructions(code):
            self.assertFalse(instr.opname.startswith("UNARY_"))

        # Verify that unfoldables are skipped
        for line, elem, opname in (
            ('-"abc"', "abc", "UNARY_NEGATIVE"),
            ('~"abc"', "abc", "UNARY_INVERT"),
        ):
            code = self.compile(line)
            self.assertInBytecode(code, "LOAD_CONST", elem)
            self.assertInBytecode(code, opname)

    def test_return(self):
        code = "def f():\n    return 42\n    x = 1"
        optcode = self.run_code(code)["f"]
        self.assertNotInBytecode(optcode, "POP_JUMP_IF_FALSE")

    def test_elim_extra_return(self):
        # RETURN LOAD_CONST None RETURN  -->  RETURN
        f = self.run_code(
            """
def f(x):
    return x"""
        )["f"]
        self.assertNotInBytecode(f, "LOAD_CONST", None)
        returns = [
            instr for instr in dis.get_instructions(f) if instr.opname == "RETURN_VALUE"
        ]
        self.assertEqual(len(returns), 1)

    def test_elim_jump_after_return1(self):
        # Eliminate dead code: jumps immediately after returns can't be reached
        f = self.run_code(
            """
def f(cond1, cond2):
    if cond1: return 1
    if cond2: return 2
    while 1:
        return 3
    while 1:
        if cond1: return 4
        return 5
    return 6"""
        )["f"]
        self.assertNotInBytecode(f, "JUMP_FORWARD")
        self.assertNotInBytecode(f, "JUMP_ABSOLUTE")
        returns = [
            instr for instr in dis.get_instructions(f) if instr.opname == "RETURN_VALUE"
        ]
        self.assertLessEqual(len(returns), 6)

    def test_elim_jump_after_return2(self):
        # Eliminate dead code: jumps immediately after returns can't be reached
        f = self.run_code(
            """
def f(cond1, cond2):
    while 1:
        if cond1: return 4"""
        )["f"]
        self.assertNotInBytecode(f, "JUMP_FORWARD")
        # There should be one jump for the while loop.
        returns = [
            instr
            for instr in dis.get_instructions(f)
            if instr.opname == "JUMP_ABSOLUTE"
        ]
        self.assertEqual(len(returns), 1)
        returns = [
            instr for instr in dis.get_instructions(f) if instr.opname == "RETURN_VALUE"
        ]
        self.assertLessEqual(len(returns), 2)

    def test_make_function_doesnt_bail(self):
        f = self.run_code(
            """
def f():
    def g()->1+1:
        pass
    return g"""
        )["f"]
        self.assertNotInBytecode(f, "BINARY_ADD")

    def test_constant_folding(self):
        # Issue #11244: aggressive constant folding.
        exprs = [
            "3 * -5",
            "-3 * 5",
            "2 * (3 * 4)",
            "(2 * 3) * 4",
            "(-1, 2, 3)",
            "(1, -2, 3)",
            "(1, 2, -3)",
            "(1, 2, -3) * 6",
            "lambda x: x in {(3 * -5) + (-1 - 6), (1, -2, 3) * 2, None}",
        ]
        for e in exprs:
            code = self.compile(e)
            for instr in dis.get_instructions(code):
                self.assertFalse(instr.opname.startswith("UNARY_"))
                self.assertFalse(instr.opname.startswith("BINARY_"))
                self.assertFalse(instr.opname.startswith("BUILD_"))


if __name__ == "__main__":
    unittest.main()
