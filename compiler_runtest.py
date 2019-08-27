#
# Helper script for testsuite - generally, run a file thru compiler and
# disassemble using dis_stable.
#
import sys
import re
import ast

import compiler.pycodegen


# https://www.python.org/dev/peps/pep-0263/
coding_re = re.compile(rb"^[ \t\f]*#.*?coding[:=][ \t]*([-_.a-zA-Z0-9]+)")

def open_with_coding(fname):
    with open(fname, "rb") as f:
        l = f.readline()
        m = coding_re.match(l)
        if not m:
            l = f.readline()
            m = coding_re.match(l)
        encoding = "utf-8"
        if m:
            encoding = m.group(1).decode()
    return open(fname, encoding=encoding)

if len(sys.argv) < 2:
    print('no filename provided')
    sys.exit(1)

peephole = True
if sys.argv[1] == '--peephole':
   peephole = True
   del sys.argv[1]

text = open_with_coding(sys.argv[1]).read()

node = ast.parse(text, sys.argv[1], "exec")
node.filename = sys.argv[1]

gen = compiler.pycodegen.ModuleCodeGenerator(node, peephole=peephole)
codeobj = gen.getCode()

import dis_stable
dis_stable.dis(codeobj)
