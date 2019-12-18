import ast
import glob
import inspect
import compiler.pycodegen
from compiler.pycodegen import compile as py_compile
from .bytecode_helper import BytecodeTestCase
from types import CodeType
from os import path
from subprocess import run, PIPE


def get_repo_root():
    dirname = path.dirname(__file__)
    completed_process = run(
        ["git", "rev-parse", "--show-toplevel"], cwd=dirname, stdout=PIPE, stderr=PIPE
    )
    if completed_process.returncode:
        print("Error occurred", file=sys.stderr)
        sys.exit(1)
    return completed_process.stdout.strip().decode("utf8")


def glob_test(dir, pattern, adder):
    base_path = path.dirname(__file__)
    target_dir = path.join(base_path, dir)
    for fname in glob.glob(path.join(target_dir, pattern), recursive=True):
        modname = path.relpath(fname, base_path)
        adder(modname, fname)


class CompilerTest(BytecodeTestCase):
    def compile(self, code, peephole_enabled=True):
        code = inspect.cleandoc("\n" + code)
        tree = ast.parse(code)
        tree.filename = ""
        gen = compiler.pycodegen.compile_module(tree, peephole_enabled)
        return gen.getCode()

    def run_code(self, code, peephole_enabled=True):
        compiled = self.compile(code, peephole_enabled)
        d = {}
        exec(compiled, d)
        return d

    def find_code(self, code):
        consts = [const for const in code.co_consts if isinstance(const, CodeType)]
        if len(consts) == 0:
            self.assertFail("No const available")
        elif len(consts) != 1:
            self.assertFail("Too many consts")
        return consts[0]

    def to_graph(self, code, peephole_enabled=True):
        code = inspect.cleandoc("\n" + code)
        tree = ast.parse(code)
        tree.filename = ""
        gen = compiler.pycodegen.compile_module(tree, peephole_enabled)
        return gen.graph
