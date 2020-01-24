import ast
from compiler.symbols import SymbolVisitor
from compiler import walk
from .common import CompilerTest


class SymbolVisitorTests(CompilerTest):
    def test_simple_assignments(self):
        stmts = [
            "foo = 42",
            "foo += 42",
            "class foo: pass",
            "def foo(): pass",
            "async def foo(): pass",
            "del foo",
            "import foo",
            "from foo import foo",
            "import bar as foo",
            "from bar import x as foo",
            "try:\n    pass\nexcept Exception as foo:\n    pass",
        ]
        for stmt in stmts:
            module = ast.parse(stmt)
            visitor = SymbolVisitor()
            walk(module, visitor)
            self.assertIn("foo", visitor.scopes[module].defs)

    def test_comp_assignments(self):
        stmts = [
            "(42 for foo in 'abc')",
            "[42 for foo in 'abc']",
            "{42 for foo in 'abc'}",
            "{42:42 for foo in 'abc'}",
        ]
        for stmt in stmts:
            module = ast.parse(stmt)
            visitor = SymbolVisitor()
            walk(module, visitor)
            gen = module.body[0].value
            self.assertIn("foo", visitor.scopes[gen].defs)


if __name__ == "__main__":
    unittest.main()
