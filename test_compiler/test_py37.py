import dis
from .common import CompilerTest
from compiler.pycodegen import Python37CodeGenerator


LOAD_METHOD = "LOAD_METHOD"
if LOAD_METHOD not in dis.opmap:
    LOAD_METHOD = "<160>"

CALL_METHOD = "CALL_METHOD"
if CALL_METHOD not in dis.opmap:
    CALL_METHOD = "<161>"

class Python37Tests(CompilerTest):
    def test_compile_method(self):
        code = self.compile('x.f()', Python37CodeGenerator)
        self.assertInBytecode(code, LOAD_METHOD)
        self.assertInBytecode(code, CALL_METHOD, 0)

        code = self.compile('x.f(42)', Python37CodeGenerator)
        self.assertInBytecode(code, LOAD_METHOD)
        self.assertInBytecode(code, CALL_METHOD, 1)

    def test_compile_method_varargs(self):
        code = self.compile('x.f(*foo)', Python37CodeGenerator)
        self.assertNotInBytecode(code, LOAD_METHOD)

    def test_compile_method_kwarg(self):
        code = self.compile('x.f(kwarg=1)', Python37CodeGenerator)
        self.assertNotInBytecode(code, LOAD_METHOD)

    def test_compile_method_normal(self):
        code = self.compile('f()', Python37CodeGenerator)
        self.assertNotInBytecode(code, LOAD_METHOD)
