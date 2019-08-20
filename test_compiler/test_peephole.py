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


if __name__ == "__main__":
    unittest.main()
