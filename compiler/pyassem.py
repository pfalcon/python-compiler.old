"""A flow graph representation for Python bytecode"""
from __future__ import print_function

import dis
import types
import sys

from typing import Any
from compiler import misc
from compiler.consts \
     import CO_OPTIMIZED, CO_NEWLOCALS, CO_VARARGS, CO_VARKEYWORDS

EXTENDED_ARG = dis.opname.index('EXTENDED_ARG')

VERSION = sys.version_info[0]
if VERSION < 3:
    def CodeType(*args):
        args = list(args)
        del args[1]
        return types.CodeType(*args)
    org_bytes = bytes
    def bytes(l):
        assert isinstance(l, list)
        return org_bytes(bytearray(l))
else:
    CodeType = types.CodeType
    long = int


def instrsize(oparg):
    if oparg <= 0xff:
        return 1
    elif oparg <= 0xffff:
        return 2
    elif oparg <= 0xffffff:
        return 3
    else:
        return 4

def cast_signed_byte_to_unsigned(i):
    if i < 0:
        i = 255 + i + 1
    return i

FVC_MASK      = 0x3
FVC_NONE      = 0x0
FVC_STR       = 0x1
FVC_REPR      = 0x2
FVC_ASCII     = 0x3
FVS_MASK      = 0x4
FVS_HAVE_SPEC = 0x4


class Instruction:
    __slots__ = ('opname', 'oparg', 'target')
    def __init__(self, opname: str, oparg: Any, target: "Block" = None):
        self.opname = opname
        self.oparg = oparg
        self.target = target

    def __repr__(self):
        if self.target:
            return f"Instruction({self.opname!r}, {self.oparg!r}, {self.target!r})"

        return f"Instruction({self.opname!r}, {self.oparg!r})"


class FlowGraph:
    def __init__(self):
        self.block_count = 0
        # List of blocks in the order they should be output for linear
        # code. As we deal with structured code, this order corresponds
        # to the order of source level constructs. (The original
        # implementation from Python2 used a complex ordering algorithm
        # which more buggy and erratic than useful.)
        self.ordered_blocks = []
        # Current block being filled in with instructions.
        self.current = None
        self.entry = Block("entry")
        self.exit = Block("exit")
        self.startBlock(self.entry)

        # Source line number to use for next instruction.
        self.lineno = 0
        # Whether line number was already output (set to False to output
        # new line number).
        self.lineno_set = False
        # First line of this code block. This field is expected to be set
        # externally and serve as a reference for generating all other
        # line numbers in the code block. (If it's not set, it will be
        # deduced).
        self.firstline = 0
        # Line number of first instruction output. Used to deduce .firstline
        # if it's not set explicitly.
        self.first_inst_lineno = 0

    def startBlock(self, block):
        if self._debug:
            if self.current:
                print("end", repr(self.current))
                print("    next", self.current.next)
                print("    prev", self.current.prev)
                print("   ", self.current.get_children())
            print(repr(block))
        block.bid = self.block_count
        self.block_count += 1
        self.current = block
        if block and block not in self.ordered_blocks:
            if block is self.exit:
                if self.ordered_blocks and self.ordered_blocks[-1].has_return():
                    return
            self.ordered_blocks.append(block)

    def nextBlock(self, block=None, label=""):
        # XXX think we need to specify when there is implicit transfer
        # from one block to the next.  might be better to represent this
        # with explicit JUMP_ABSOLUTE instructions that are optimized
        # out when they are unnecessary.
        #
        # I think this strategy works: each block has a child
        # designated as "next" which is returned as the last of the
        # children.  because the nodes in a graph are emitted in
        # reverse post order, the "next" block will always be emitted
        # immediately after its parent.
        # Worry: maintaining this invariant could be tricky
        if block is None:
            block = self.newBlock(label=label)

        # Note: If the current block ends with an unconditional control
        # transfer, then it is techically incorrect to add an implicit
        # transfer to the block graph. Doing so results in code generation
        # for unreachable blocks.  That doesn't appear to be very common
        # with Python code and since the built-in compiler doesn't optimize
        # it out we don't either.
        self.current.addNext(block)
        self.startBlock(block)

    def newBlock(self, label=""):
        b = Block(label)
        return b

    def startExitBlock(self):
        self.startBlock(self.exit)

    _debug = 0

    def _enable_debug(self):
        self._debug = 1

    def _disable_debug(self):
        self._debug = 0

    def emit(self, opcode, oparg = 0):
        if not self.lineno_set and self.lineno:
            self.lineno_set = True
            self.emit('SET_LINENO', self.lineno)

        if self._debug:
            print("\t", inst)

        if opcode != "SET_LINENO" and isinstance(oparg, Block):
            self.current.addOutEdge(oparg)
            self.current.emit(Instruction(opcode, 0, oparg))
            return

        self.current.emit(Instruction(opcode, oparg))


        if opcode == "SET_LINENO" and not self.first_inst_lineno:
            self.first_inst_lineno = oparg

    def getBlocksInOrder(self):
        """Return the blocks in the order they should be output."""
        return self.ordered_blocks

    def getBlocks(self):
        if self.exit not in self.ordered_blocks:
            return self.ordered_blocks + [self.exit]
        return self.ordered_blocks

    def getRoot(self):
        """Return nodes appropriate for use with dominator"""
        return self.entry

    def getContainedGraphs(self):
        l = []
        for b in self.getBlocks():
            l.extend(b.getContainedGraphs())
        return l


class Block:
    def __init__(self, label=''):
        self.insts = []
        self.outEdges = set()
        self.label = label
        self.bid = None
        self.next = []
        self.prev = []
        self.offset = 0

    def __repr__(self):
        if self.label:
            return "<block %s id=%d>" % (self.label, self.bid)
        else:
            return "<block id=%d>" % (self.bid)

    def __str__(self):
        insts = map(str, self.insts)
        return "<block %s %d:\n%s>" % (self.label, self.bid,
                                       '\n'.join(insts))

    def emit(self, instr):
        self.insts.append(instr)

    def getInstructions(self):
        return self.insts

    def addOutEdge(self, block):
        self.outEdges.add(block)

    def addNext(self, block):
        self.next.append(block)
        assert len(self.next) == 1, map(str, self.next)
        block.prev.append(self)
        assert len(block.prev) == 1, map(str, block.prev)

    _uncond_transfer = ('RETURN_VALUE', 'RAISE_VARARGS',
                        'JUMP_ABSOLUTE', 'JUMP_FORWARD', 'CONTINUE_LOOP',
                        )

    def has_unconditional_transfer(self):
        """Returns True if there is an unconditional transfer to an other block
        at the end of this block. This means there is no risk for the bytecode
        executer to go past this block's bytecode."""
        if self.insts and self.insts[-1][0] in self._uncond_transfer:
            return True

    def has_return(self):
        return self.insts and self.insts[-1].opname == "RETURN_VALUE"

    def get_children(self):
        return list(self.outEdges) + self.next

    def get_followers(self):
        """Get the whole list of followers, including the next block."""
        followers = set(self.next)
        # Blocks that must be emitted *after* this one, because of
        # bytecode offsets (e.g. relative jumps) pointing to them.
        for inst in self.insts:
            if inst[0] in PyFlowGraph.hasjrel:
                followers.add(inst[1])
        return followers

    def getContainedGraphs(self):
        """Return all graphs contained within this block.

        For example, a MAKE_FUNCTION block will contain a reference to
        the graph for the function body.
        """
        contained = []
        for inst in self.insts:
            if len(inst) == 1:
                continue
            op = inst[1]
            if hasattr(op, 'graph'):
                contained.append(op.graph)
        return contained

# flags for code objects

# the FlowGraph is transformed in place; it exists in one of these states
RAW = "RAW"
FLAT = "FLAT"
CONV = "CONV"
DONE = "DONE"

class PyFlowGraph(FlowGraph):
    super_init = FlowGraph.__init__

    def __init__(self, name, filename, args=(), kwonlyargs=(), starargs=(), optimized=0, klass=None):
        self.super_init()
        self.name = name
        self.filename = filename
        self.docstring = None
        self.args = args
        self.kwonlyargs = kwonlyargs
        self.starargs = starargs
        self.klass = klass
        if optimized:
            self.flags = CO_OPTIMIZED | CO_NEWLOCALS
        else:
            self.flags = 0
        self.consts = []
        self.names = []
        # Free variables found by the symbol table scan, including
        # variables used only in nested scopes, are included here.
        self.freevars = []
        self.cellvars = []
        # The closure list is used to track the order of cell
        # variables and free variables in the resulting code object.
        # The offsets used by LOAD_CLOSURE/LOAD_DEREF refer to both
        # kinds of variables.
        self.closure = []
        self.varnames = list(args) + list(kwonlyargs) + list(starargs)
        self.stage = RAW
        self.first_inst_lineno = 0
        self.lineno_set = False
        self.lineno = 0

    def setDocstring(self, doc):
        self.docstring = doc

    def setFlag(self, flag):
        self.flags = self.flags | flag

    def checkFlag(self, flag):
        if self.flags & flag:
            return 1

    def setFreeVars(self, names):
        self.freevars = list(names)

    def setCellVars(self, names):
        self.cellvars = names

    def getCode(self):
        """Get a Python code object"""
        assert self.stage == RAW
        self.computeStackDepth()
        # We need to convert into numeric opargs before flattening so we
        # know the sizes of our opargs
        self.convertArgs()
        assert self.stage == CONV
        self.flattenGraph()
        assert self.stage == FLAT
        self.makeByteCode()
        assert self.stage == DONE
        return self.newCodeObject()

    def dump(self, io=None):
        if io:
            save = sys.stdout
            sys.stdout = io
        pc = 0
        for t in self.insts:
            opname = t[0]
            if opname == "SET_LINENO":
                print()
            if len(t) == 1:
                print("\t", "%3d" % pc, opname)
                pc = pc + 1
            else:
                print("\t", "%3d" % pc, opname, t[1])
                pc = pc + 3
        if io:
            sys.stdout = save

    def computeStackDepth(self):
        """Compute the max stack depth.

        Approach is to compute the stack effect of each basic block.
        Then find the path through the code with the largest total
        effect.
        """
        depth = {}
        exit = None
        for b in self.getBlocks():
            depth[b] = findDepth(b.getInstructions())

        seen = {}

        def max_depth(b, d):
            if b in seen:
                return d
            seen[b] = 1
            d = d + depth[b]
            children = b.get_children()
            if children:
                return max([max_depth(c, d) for c in children])
            else:
                if not b.label == "exit":
                    return max_depth(self.exit, d)
                else:
                    return d

        self.stacksize = max_depth(self.entry, 0)

    def flattenGraph(self):
        """Arrange the blocks in order and resolve jumps"""
        assert self.stage == CONV
        # This is an awful hack that could hurt performance, but
        # on the bright side it should work until we come up
        # with a better solution.
        #
        # The issue is that in the first loop blocksize() is called
        # which calls instrsize() which requires i_oparg be set
        # appropriately. There is a bootstrap problem because
        # i_oparg is calculated in the second loop.
        #
        # So we loop until we stop seeing new EXTENDED_ARGs.
        # The only EXTENDED_ARGs that could be popping up are
        # ones in jump instructions.  So this should converge
        # fairly quickly.
        extended_arg_recompile = True
        while extended_arg_recompile:
            extended_arg_recompile = False
            self.insts = insts = []
            pc = 0
            for b in self.getBlocksInOrder():
                b.offset = pc

                for inst in b.getInstructions():
                    insts.append(inst)
                    if inst.opname != "SET_LINENO" :
                        pc += instrsize(inst.oparg)

            pc = 0
            for inst in insts:
                if inst.opname != "SET_LINENO":
                    pc += instrsize(inst.oparg)

                opname = inst.opname
                if opname in self.hasjrel or opname in self.hasjabs:
                    oparg = inst.oparg
                    target = inst.target

                    offset = target.offset
                    if opname in self.hasjrel:
                        offset -= pc

                    offset *= 2
                    if instrsize(oparg) != instrsize(offset):
                        extended_arg_recompile = True

                    assert offset >= 0, "Offset value: %d" % offset
                    inst.oparg = offset
        self.stage = FLAT

    hasjrel = set()
    for i in dis.hasjrel:
        hasjrel.add(dis.opname[i])
    hasjabs = set()
    for i in dis.hasjabs:
        hasjabs.add(dis.opname[i])

    def convertArgs(self):
        """Convert arguments from symbolic to concrete form"""
        assert self.stage == RAW
        # Docstring is first entry in co_consts for normal functions
        # (Other types of code objects deal with docstrings in different
        # manner, e.g. lambdas and comprehensions don't have docstrings,
        # classes store them as __doc__ attribute.
        if self.name == "<lambda>" or (not self.name.startswith("<") and not self.klass):
            self.consts.insert(0, self.docstring)
        self.sort_cellvars()

        for b in self.getBlocksInOrder():
            for instr in b.insts:
                conv = self._converters.get(instr.opname)
                if conv:
                    instr.oparg = conv(self, instr.oparg)

        self.stage = CONV

    def sort_cellvars(self):
        self.closure = self.cellvars + self.freevars

    def _lookupName(self, name, list):
        """Return index of name in list, appending if necessary

        This routine uses a list instead of a dictionary, because a
        dictionary can't store two different keys if the keys have the
        same value but different types, e.g. 2 and 2L.  The compiler
        must treat these two separately, so it does an explicit type
        comparison before comparing the values.
        """
        t = type(name)
        for i in range(len(list)):
            if t == type(list[i]) and list[i] == name:
                return i
        end = len(list)
        list.append(name)
        return end

    _converters = {}
    def _convert_LOAD_CONST(self, arg):
        if hasattr(arg, 'getCode'):
            arg = arg.getCode()
        return self._lookupName(arg, self.consts)

    def _convert_LOAD_FAST(self, arg):
        return self._lookupName(arg, self.varnames)
    _convert_STORE_FAST = _convert_LOAD_FAST
    _convert_DELETE_FAST = _convert_LOAD_FAST

    def _convert_LOAD_NAME(self, arg):
        return self._lookupName(arg, self.names)

    def _convert_NAME(self, arg):
        return self._lookupName(arg, self.names)
    _convert_STORE_NAME = _convert_NAME
    _convert_STORE_ANNOTATION = _convert_NAME
    _convert_DELETE_NAME = _convert_NAME
    _convert_IMPORT_NAME = _convert_NAME
    _convert_IMPORT_FROM = _convert_NAME
    _convert_STORE_ATTR = _convert_NAME
    _convert_LOAD_ATTR = _convert_NAME
    _convert_DELETE_ATTR = _convert_NAME

    def _convert_GLOBAL(self, arg):
        return self._lookupName(arg, self.names)
    _convert_LOAD_GLOBAL = _convert_GLOBAL
    _convert_STORE_GLOBAL = _convert_GLOBAL
    _convert_DELETE_GLOBAL = _convert_GLOBAL

    def _convert_DEREF(self, arg):
        # Sometimes, both cellvars and freevars may contain the same var
        # (e.g., for class' __class__). In this case, prefer freevars.
        if arg in self.freevars:
            return self._lookupName(arg, self.freevars) + len(self.cellvars)
        return self._lookupName(arg, self.closure)
    _convert_LOAD_DEREF = _convert_DEREF
    _convert_STORE_DEREF = _convert_DEREF
    _convert_DELETE_DEREF = _convert_DEREF
    _convert_LOAD_CLASSDEREF = _convert_DEREF

    def _convert_LOAD_CLOSURE(self, arg):
        return self._lookupName(arg, self.closure)

    _cmp = list(dis.cmp_op)
    def _convert_COMPARE_OP(self, arg):
        return self._cmp.index(arg)

    # similarly for other opcodes...

    name = obj = opname = None
    for name, obj in locals().items():
        if name[:9] == "_convert_":
            opname = name[9:]
            _converters[opname] = obj
    del name, obj, opname

    def makeByteCode(self):
        assert self.stage == FLAT
        self.lnotab = lnotab = LineAddrTable()
        lnotab.setFirstLine(self.firstline or self.first_inst_lineno or 1)

        for t in self.insts:
            if t.opname == "SET_LINENO":
                lnotab.nextLine(t.oparg)
                continue

            oparg = t.oparg
            try:
                assert 0 <= oparg <= 0xffffffff
                if oparg > 0xffffff:
                    lnotab.addCode(EXTENDED_ARG, (oparg >> 24) & 0xff)
                if oparg > 0xffff:
                    lnotab.addCode(EXTENDED_ARG, (oparg >> 16) & 0xff)
                if oparg > 0xff:
                    lnotab.addCode(EXTENDED_ARG, (oparg >> 8) & 0xff)
                lnotab.addCode(self.opnum[t.opname], oparg & 0xff)
            except ValueError:
                print(t.opname, oparg)
                print(self.opnum[t.opname], oparg)
                raise
        self.stage = DONE

    opnum = {}
    for num in range(len(dis.opname)):
        opnum[dis.opname[num]] = num
    del num

    def newCodeObject(self):
        assert self.stage == DONE
        if (self.flags & CO_NEWLOCALS) == 0:
            nlocals = 0
        else:
            nlocals = len(self.varnames)

        firstline = self.firstline
        # For module, .firstline is initially not set, and should be first
        # line with actual bytecode instruction (skipping docstring, optimized
        # out instructions, etc.)
        if not firstline:
            firstline = self.first_inst_lineno
        # If no real instruction, fallback to 1
        if not firstline:
            firstline = 1

        return CodeType(len(self.args), len(self.kwonlyargs), nlocals,
                        self.stacksize, self.flags,
                        self.lnotab.getCode(), self.getConsts(),
                        tuple(self.names), tuple(self.varnames),
                        self.filename, self.name, firstline,
                        self.lnotab.getTable(), tuple(self.freevars),
                        tuple(self.cellvars))

    def getConsts(self):
        """Return a tuple for the const slot of the code object

        Must convert references to code (MAKE_FUNCTION) to code
        objects recursively.
        """
        l = []
        for elt in self.consts:
            if isinstance(elt, PyFlowGraph):
                elt = elt.getCode()
            l.append(elt)
        return tuple(l)

def isJump(opname):
    if opname[:4] == 'JUMP':
        return 1


def twobyte(val):
    """Convert an int argument into high and low bytes"""
    assert isinstance(val, (int, long))
    return divmod(val, 256)

class LineAddrTable:
    """lnotab

    This class builds the lnotab, which is documented in compile.c.
    Here's a brief recap:

    For each SET_LINENO instruction after the first one, two bytes are
    added to lnotab.  (In some cases, multiple two-byte entries are
    added.)  The first byte is the distance in bytes between the
    instruction for the last SET_LINENO and the current SET_LINENO.
    The second byte is offset in line numbers.  If either offset is
    greater than 255, multiple two-byte entries are added -- see
    compile.c for the delicate details.
    """

    def __init__(self):
        self.code = []
        self.codeOffset = 0
        self.firstline = 0
        self.lastline = 0
        self.lastoff = 0
        self.lnotab = []

    def setFirstLine(self, lineno):
        self.firstline = lineno
        self.lastline = lineno

    def addCode(self, opcode, oparg):
        self.code.append(opcode)
        self.code.append(oparg)
        self.codeOffset += 2

    def nextLine(self, lineno):
        if self.firstline == 0:
            self.firstline = lineno
            self.lastline = lineno
        else:
            # compute deltas
            addr_delta = self.codeOffset - self.lastoff
            line_delta = lineno - self.lastline
            if not addr_delta and not line_delta:
                return

            push = self.lnotab.append
            while addr_delta > 255:
                push(255); push(0)
                addr_delta -= 255
            if line_delta < -128 or 127 < line_delta:
                if line_delta < 0:
                    k = -128
                    ncodes = (-line_delta) // 128
                else:
                    k = 127
                    ncodes = line_delta // 127
                line_delta -= ncodes * 127
                push(addr_delta); push(cast_signed_byte_to_unsigned(k))
                addr_delta = 0
                for j in range(ncodes - 1):
                    push(0); push(cast_signed_byte_to_unsigned(k))

            push(addr_delta); push(cast_signed_byte_to_unsigned(line_delta))

            self.lastline = lineno
            self.lastoff = self.codeOffset

    def getCode(self):
        return bytes(self.code)

    def getTable(self):
        return bytes(self.lnotab)

class StackDepthTracker:
    # XXX 1. need to keep track of stack depth on jumps
    # XXX 2. at least partly as a result, this code is broken

    def findDepth(self, insts, debug=0):
        depth = 0
        maxDepth = 0
        for i in insts:
            opname = i.opname
            if debug:
                print(i, end="")
            delta = self.effect.get(opname, None)
            if delta is not None:
                depth = depth + delta
            else:
                # now check patterns
                for pat, pat_delta in self.patterns:
                    if opname[:len(pat)] == pat:
                        delta = pat_delta
                        depth = depth + delta
                        break
                # if we still haven't found a match
                if delta is None:
                    meth = getattr(self, opname, None)
                    if meth is not None:
                        depth = depth + meth(i.oparg)
            if depth > maxDepth:
                maxDepth = depth
            if debug:
                print(depth, maxDepth)
        return maxDepth

    effect = {
        'POP_TOP': -1,
        'DUP_TOP': 1,
        'LIST_APPEND': -1,
        'SET_ADD': -1,
        'MAP_ADD': -2,
        'SLICE+1': -1,
        'SLICE+2': -1,
        'SLICE+3': -2,
        'STORE_SLICE+0': -1,
        'STORE_SLICE+1': -2,
        'STORE_SLICE+2': -2,
        'STORE_SLICE+3': -3,
        'DELETE_SLICE+0': -1,
        'DELETE_SLICE+1': -2,
        'DELETE_SLICE+2': -2,
        'DELETE_SLICE+3': -3,
        'STORE_SUBSCR': -3,
        'DELETE_SUBSCR': -2,
        # PRINT_EXPR?
        'PRINT_ITEM': -1,
        'RETURN_VALUE': -1,
        'YIELD_VALUE': -1,
        'EXEC_STMT': -3,
        'BUILD_CLASS': -2,
        'STORE_NAME': -1,
        'STORE_ATTR': -2,
        'DELETE_ATTR': -1,
        'STORE_GLOBAL': -1,
        'BUILD_MAP': 1,
        'COMPARE_OP': -1,
        'STORE_FAST': -1,
        'IMPORT_STAR': -1,
        'IMPORT_NAME': -1,
        'IMPORT_FROM': 1,
        'LOAD_ATTR': 0, # unlike other loads
        # close enough...
        'SETUP_EXCEPT': 3,
        'SETUP_FINALLY': 3,
        'FOR_ITER': 1,
        'WITH_CLEANUP': -1,
        'JUMP_IF_TRUE_OR_POP': -1, # approximation
        'JUMP_IF_FALSE_OR_POP': -1, # approximation
        }
    # use pattern match
    patterns = [
        ('BINARY_', -1),
        ('LOAD_', 1),
        ]

    def UNPACK_SEQUENCE(self, count):
        return count-1
    def BUILD_TUPLE(self, count):
        return -count+1
    def BUILD_LIST(self, count):
        return -count+1
    def BUILD_SET(self, count):
        return -count+1
    def CALL_FUNCTION(self, argc):
        hi, lo = divmod(argc, 256)
        return -(lo + hi * 2)
    def CALL_FUNCTION_VAR(self, argc):
        return self.CALL_FUNCTION(argc)-1
    def CALL_FUNCTION_KW(self, argc):
        return self.CALL_FUNCTION(argc)-1
    def CALL_FUNCTION_VAR_KW(self, argc):
        return self.CALL_FUNCTION(argc)-2
    def MAKE_FUNCTION(self, oparg):
        return -1 - ((oparg & 0x01) != 0) - ((oparg & 0x02) != 0) - ((oparg & 0x04) != 0) - ((oparg & 0x08) != 0)
    def MAKE_CLOSURE(self, argc):
        # XXX need to account for free variables too!
        return -argc
    def BUILD_SLICE(self, argc):
        if argc == 2:
            return -1
        elif argc == 3:
            return -2
    def FORMAT_VALUE(self, argc):
        return -1 if (argc & FVS_MASK) == FVS_HAVE_SPEC else 0
    def BUILD_STRING(self, argc):
        return 1 - argc

    def DUP_TOPX(self, argc):
        return argc

findDepth = StackDepthTracker().findDepth
