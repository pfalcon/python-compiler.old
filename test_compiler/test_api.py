import unittest
from unittest import TestCase
from .common import CompilerTest
import dis
from dis import opmap, opname
import ast
from compiler import compile


class ApiTests(CompilerTest):
    def test_compile_single(self):
        code = compile('42', 'foo', 'single')
        self.assertInBytecode(code, 'LOAD_CONST', 42)
        self.assertInBytecode(code, 'PRINT_EXPR')

    def test_compile_eval(self):
        code = compile('42', 'foo', 'eval')
        self.assertInBytecode(code, 'LOAD_CONST', 42)
        self.assertInBytecode(code, 'RETURN_VALUE')

if __name__ == "__main__":
    unittest.main()
