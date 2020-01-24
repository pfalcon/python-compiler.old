import dis
from .common import CompilerTest
from compiler.pycodegen import CodeGenerator, Python37CodeGenerator
from compiler.consts import (
    CO_OPTIMIZED,
    CO_NOFREE,
    CO_NEWLOCALS,
    CO_FUTURE_GENERATOR_STOP,
    CO_FUTURE_ANNOTATIONS,
)


LOAD_METHOD = "LOAD_METHOD"
if LOAD_METHOD not in dis.opmap:
    LOAD_METHOD = "<160>"

CALL_METHOD = "CALL_METHOD"
if CALL_METHOD not in dis.opmap:
    CALL_METHOD = "<161>"
STORE_ANNOTATION = "STORE_ANNOTATION"
if STORE_ANNOTATION not in dis.opmap:
    STORE_ANNOTATION = "<0>"

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

    def test_future_gen_stop(self):
        code = self.compile("from __future__ import generator_stop", Python37CodeGenerator)
        self.assertEqual(
            code.co_flags,
            CO_NOFREE,
        )

    def test_future_annotations_flag(self):
        code = self.compile("from __future__ import annotations", Python37CodeGenerator)
        self.assertEqual(
            code.co_flags,
            CO_NOFREE |  CO_FUTURE_ANNOTATIONS,
        )

    def test_future_annotations(self):
        annotations = ["42"]
        for annotation in annotations:
            code = self.compile(f"from __future__ import annotations\ndef f() -> {annotation}:\n    pass", Python37CodeGenerator)
            self.assertInBytecode(code, 'LOAD_CONST', annotation)
        self.assertEqual(
            code.co_flags,
            CO_NOFREE |  CO_FUTURE_ANNOTATIONS,
        )

    def test_circular_import_as(self):
        """verifies that we emit an IMPORT_FROM to enable circular imports
        when compiling an absolute import to verify that they can support
        circular imports"""
        code = self.compile(f"import x.y as b", Python37CodeGenerator)
        self.assertInBytecode(code, 'IMPORT_FROM')
        self.assertNotInBytecode(code, 'LOAD_ATTR')

        code = self.compile(f"import x.y as b", CodeGenerator)
        self.assertNotInBytecode(code, 'IMPORT_FROM')
        self.assertInBytecode(code, 'LOAD_ATTR')

    def test_store_annotation_removed(self):
        code = self.compile(f"class C:\n    x: int = 42", Python37CodeGenerator)
        class_code = self.find_code(code)
        self.assertNotInBytecode(class_code, STORE_ANNOTATION)

        code = self.compile(f"class C:\n    x: int = 42", CodeGenerator)
        class_code = self.find_code(code)
        self.assertInBytecode(class_code, STORE_ANNOTATION)

    def test_compile_opt_unary_jump(self):
        graph = self.to_graph('if not abc: foo', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'POP_JUMP_IF_FALSE')

        graph = self.to_graph('if not abc: foo', CodeGenerator)
        self.assertInGraph(graph, 'POP_JUMP_IF_FALSE')

    def test_compile_opt_bool_or_jump(self):
        graph = self.to_graph('if abc or bar: foo', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'JUMP_IF_TRUE_OR_POP')

        graph = self.to_graph('if abc or bar: foo', CodeGenerator)
        self.assertInGraph(graph, 'JUMP_IF_TRUE_OR_POP')

    def test_compile_opt_bool_and_jump(self):
        graph = self.to_graph('if abc and bar: foo', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'JUMP_IF_FALSE_OR_POP')

        graph = self.to_graph('if abc and bar: foo', CodeGenerator)
        self.assertInGraph(graph, 'JUMP_IF_FALSE_OR_POP')

    def test_compile_opt_assert_or_bool(self):
        graph = self.to_graph('assert abc or bar', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'JUMP_IF_TRUE_OR_POP')

        graph = self.to_graph('assert abc or bar', CodeGenerator)
        self.assertInGraph(graph, 'JUMP_IF_TRUE_OR_POP')

    def test_compile_opt_assert_and_bool(self):
        graph = self.to_graph('assert abc and bar', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'JUMP_IF_FALSE_OR_POP')

        graph = self.to_graph('assert abc and bar', CodeGenerator)
        self.assertInGraph(graph, 'JUMP_IF_FALSE_OR_POP')

    def test_compile_opt_if_exp(self):
        graph = self.to_graph('assert not a if c else b', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'UNARY_NOT')

        graph = self.to_graph('assert not a if c else b', CodeGenerator)
        self.assertInGraph(graph, 'UNARY_NOT')

    def test_compile_opt_cmp_op(self):
        graph = self.to_graph('assert not a > b', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'UNARY_NOT')

        graph = self.to_graph('assert not a > b', CodeGenerator)
        self.assertInGraph(graph, 'UNARY_NOT')

    def test_compile_opt_chained_cmp_op(self):
        graph = self.to_graph('assert not a > b > c', Python37CodeGenerator)
        self.assertNotInGraph(graph, 'UNARY_NOT')

        graph = self.to_graph('assert not a > b > c', CodeGenerator)
        self.assertInGraph(graph, 'UNARY_NOT')
