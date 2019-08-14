import ast
import glob
import compiler.pycodegen
from .bytecode_helper import BytecodeTestCase
from types import CodeType
from os import path
from subprocess import run, PIPE


def glob_test(dir, pattern, adder):
    base_path = path.dirname(__file__)
    target_dir = path.join(base_path, dir)
    for fname in glob.glob(path.join(target_dir, pattern), recursive=True):
        modname = path.relpath(fname, base_path)
        adder(modname, fname)


class CompilerTest(BytecodeTestCase):
    def to_graph(self, code):
        tree = ast.parse(code)
        tree.filename = ""
        gen = compiler.pycodegen.ModuleCodeGenerator(tree)
        return gen.graph
