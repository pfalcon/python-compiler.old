#!/usr/bin/env python3
#
# Dissassemble code objects:
# a) recursively (like dis.dis() in Python3.7 behaves);
# b) providing stable references to internal code objects (by replacing
#    memory address with incrementing number);
# c) besides disassembly, also dump other fields of code objects.
# Useful for comparing disassembly outputs from different runs.
#
from __future__ import print_function
import re
import dis as _dis


id_map = {}
id_cnt = 0


def get_co_id(co):
    global id_cnt
    addr = id(co)
    if addr in id_map:
        return id_map[addr]
    id_map[addr] = id_cnt
    id_cnt += 1
    return id_cnt - 1


def co_repr(co):
    return '<code object %s at #%d, file "%s", line %d>' % (co.co_name, get_co_id(co), co.co_filename, co.co_firstlineno)


def disassemble(co, lasti=-1, file=None):
    """Disassemble a code object."""
    cell_names = co.co_cellvars + co.co_freevars
    linestarts = dict(_dis.findlinestarts(co))
    consts = [co_repr(x) if hasattr(x, "co_code") else x for x in co.co_consts]
    _dis._disassemble_bytes(co.co_code, lasti, co.co_varnames, co.co_names,
                       consts, cell_names, linestarts, file=file)

def dis(co):
    print(co_repr(co))
    disassemble(co)
    print("co_argcount:", co.co_argcount)
    print("co_kwonlyargcount:", co.co_kwonlyargcount)
    print("co_stacksize:", co.co_stacksize)
#    print("co_flags:", hex(co.co_flags))
    print("co_consts:", tuple([co_repr(x) if hasattr(x, "co_code") else x for x in co.co_consts]))
    print("co_firstlineno:", co.co_firstlineno)
    print("co_names:", co.co_names)
    print("co_varnames:", co.co_varnames)
    print("co_cellvars:", co.co_cellvars)
    print("co_freevars:", co.co_freevars)
    print("co_lnotab:", co.co_lnotab)
    print()
    for c in co.co_consts:
        if hasattr(c, "co_code"):
            dis(c)


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


if __name__ == "__main__":
    import sys
    with open_with_coding(sys.argv[1]) as f:
        co = compile(f.read(), sys.argv[1], "exec")
    dis(co)
