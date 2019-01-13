from __future__ import print_function
import imp
import os
import marshal
import struct
import sys
from io import StringIO

import ast
from compiler import parse, walk, syntax
from compiler import pyassem, misc, future, symbols
from compiler.consts import SC_LOCAL, SC_GLOBAL_IMPLICIT, SC_GLOBAL_EXPLICIT, \
     SC_FREE, SC_CELL
from compiler.consts import (CO_VARARGS, CO_VARKEYWORDS, CO_NEWLOCALS,
     CO_NESTED, CO_GENERATOR, CO_FUTURE_DIVISION,
     CO_FUTURE_ABSIMPORT, CO_FUTURE_WITH_STATEMENT, CO_FUTURE_PRINT_FUNCTION)
from compiler.pyassem import TupleArg

from . import config

# XXX The version-specific code can go, since this code only works with 2.x.
# Do we have Python 1.x or Python 2.x?
try:
    VERSION = sys.version_info[0]
except AttributeError:
    VERSION = 1

callfunc_opcode_info = {
    # (Have *args, Have **args) : opcode
    (0,0) : "CALL_FUNCTION",
    (1,0) : "CALL_FUNCTION_VAR",
    (0,1) : "CALL_FUNCTION_KW",
    (1,1) : "CALL_FUNCTION_VAR_KW",
}

LOOP = 1
EXCEPT = 2
TRY_FINALLY = 3
END_FINALLY = 4

def compileFile(filename, display=0):
    f = open(filename, 'U')
    buf = f.read()
    f.close()
    mod = Module(buf, filename)
    try:
        mod.compile(display)
    except SyntaxError:
        raise
    else:
        f = open(filename + "c", "wb")
        mod.dump(f)
        f.close()

def compile(source, filename, mode, flags=None, dont_inherit=None):
    """Replacement for builtin compile() function"""
    if flags is not None or dont_inherit is not None:
        raise RuntimeError("not implemented yet")

    if mode == "single":
        gen = Interactive(source, filename)
    elif mode == "exec":
        gen = Module(source, filename)
    elif mode == "eval":
        gen = Expression(source, filename)
    else:
        raise ValueError("compile() 3rd arg must be 'exec' or "
                         "'eval' or 'single'")
    gen.compile()
    return gen.code

class AbstractCompileMode:

    mode = None # defined by subclass

    def __init__(self, source, filename):
        self.source = source
        self.filename = filename
        self.code = None

    def _get_tree(self):
        tree = parse(self.source, self.mode)
        misc.set_filename(self.filename, tree)
        syntax.check(tree)
        return tree

    def compile(self):
        pass # implemented by subclass

    def getCode(self):
        return self.code

class Expression(AbstractCompileMode):

    mode = "eval"

    def compile(self):
        tree = self._get_tree()
        gen = ExpressionCodeGenerator(tree)
        self.code = gen.getCode()

class Interactive(AbstractCompileMode):

    mode = "single"

    def compile(self):
        tree = self._get_tree()
        gen = InteractiveCodeGenerator(tree)
        self.code = gen.getCode()

class Module(AbstractCompileMode):

    mode = "exec"

    def compile(self, display=0):
        tree = self._get_tree()
        gen = ModuleCodeGenerator(tree)
        if display:
            import pprint
            pprint.pprint(tree)
        self.code = gen.getCode()

    def dump(self, f):
        f.write(self.getPycHeader())
        marshal.dump(self.code, f)

    MAGIC = imp.get_magic()

    def getPycHeader(self):
        # compile.c uses marshal to write a long directly, with
        # calling the interface that would also generate a 1-byte code
        # to indicate the type of the value.  simplest way to get the
        # same effect is to call marshal and then skip the code.
        mtime = os.path.getmtime(self.filename)
        mtime = struct.pack('<i', mtime)
        return self.MAGIC + mtime

class LocalNameFinder:
    """Find local names in scope"""
    def __init__(self, names=()):
        self.names = misc.Set()
        self.globals = misc.Set()
        for name in names:
            self.names.add(name)

    # XXX list comprehensions and for loops

    def getLocals(self):
        for elt in self.globals.elements():
            if self.names.has_elt(elt):
                self.names.remove(elt)
        return self.names

    def visitDict(self, node):
        pass

    def visitGlobal(self, node):
        for name in node.names:
            self.globals.add(name)

    def visitFunctionDef(self, node):
        self.names.add(node.name)

    def visitLambda(self, node):
        pass

    def visitImport(self, node):
        for alias in node.names:
            self.names.add(alias.asname or alias.name)

    def visitImportFrom(self, node):
        for alias in node.names:
            self.names.add(alias.asname or alias.name)

    def visitClassDef(self, node):
        self.names.add(node.name)

    def visitAssName(self, node):
        self.names.add(node.name)

    def visitName(self, node):
        if isinstance(node.ctx, ast.Store):
            self.names.add(node.id)

def is_constant_false(node):
    if isinstance(node, ast.Num):
        if not node.n:
            return 1
    return 0


def is_constant_true(node):
    if isinstance(node, ast.Num):
        if node.n:
            return 1
    return 0


class CodeGenerator:
    """Defines basic code generator for Python bytecode

    This class is an abstract base class.  Concrete subclasses must
    define an __init__() that defines self.graph and then calls the
    __init__() defined in this class.

    The concrete class must also define the class attributes
    NameFinder, FunctionGen, and ClassGen.  These attributes can be
    defined in the initClass() method, which is a hook for
    initializing these methods after all the classes have been
    defined.
    """

    optimized = 0 # is namespace access optimized?
    __initialized = None
    class_name = None # provide default for instance variable

    def __init__(self):
        if self.__initialized is None:
            self.initClass()
            self.__class__.__initialized = 1
        self.checkClass()
        self.locals = misc.Stack()
        self.setups = misc.Stack()
        self.last_lineno = None
        self._setupGraphDelegation()
        self._div_op = "BINARY_DIVIDE"

        # XXX set flags based on future features
        futures = self.get_module().futures
        for feature in futures:
            if feature == "division":
                self.graph.setFlag(CO_FUTURE_DIVISION)
                self._div_op = "BINARY_TRUE_DIVIDE"
            elif feature == "absolute_import":
                self.graph.setFlag(CO_FUTURE_ABSIMPORT)
            elif feature == "with_statement":
                self.graph.setFlag(CO_FUTURE_WITH_STATEMENT)
            elif feature == "print_function":
                self.graph.setFlag(CO_FUTURE_PRINT_FUNCTION)

    def initClass(self):
        """This method is called once for each class"""

    def checkClass(self):
        """Verify that class is constructed correctly"""
        try:
            assert hasattr(self, 'graph')
            assert getattr(self, 'NameFinder')
            assert getattr(self, 'FunctionGen')
            assert getattr(self, 'ClassGen')
        except AssertionError:
            intro = "Bad class construction for %s" % self.__class__.__name__
            raise AssertionError(intro)

    def _setupGraphDelegation(self):
        self.emit = self.graph.emit
        self.newBlock = self.graph.newBlock
        self.startBlock = self.graph.startBlock
        self.nextBlock = self.graph.nextBlock
        self.setDocstring = self.graph.setDocstring

    def getCode(self):
        """Return a code object"""
        return self.graph.getCode()

    def mangle(self, name):
        if self.class_name is not None:
            return misc.mangle(name, self.class_name)
        else:
            return name

    def parseSymbols(self, tree):
        s = symbols.SymbolVisitor()
        walk(tree, s)
        return s.scopes

    def get_module(self):
        raise RuntimeError("should be implemented by subclasses")

    # Next five methods handle name access

    def isLocalName(self, name):
        return self.locals.top().has_elt(name)

    def storeName(self, name):
        self._nameOp('STORE', name)

    def loadName(self, name):
        self._nameOp('LOAD', name)

    def delName(self, name):
        self._nameOp('DELETE', name)

    def _nameOp(self, prefix, name):
        name = self.mangle(name)
        scope = self.scope.check_name(name)
        if scope == SC_LOCAL:
            if not self.optimized:
                self.emit(prefix + '_NAME', name)
            else:
                self.emit(prefix + '_FAST', name)
        elif scope == SC_GLOBAL_EXPLICIT:
            self.emit(prefix + '_GLOBAL', name)
        elif scope == SC_GLOBAL_IMPLICIT:
            if not self.optimized:
                self.emit(prefix + '_NAME', name)
            else:
                self.emit(prefix + '_GLOBAL', name)
        elif scope == SC_FREE or scope == SC_CELL:
            self.emit(prefix + '_DEREF', name)
        else:
            raise RuntimeError("unsupported scope for var %s: %d" % \
                  (name, scope))

    def _implicitNameOp(self, prefix, name):
        """Emit name ops for names generated implicitly by for loops

        The interpreter generates names that start with a period or
        dollar sign.  The symbol table ignores these names because
        they aren't present in the program text.
        """
        if self.optimized:
            self.emit(prefix + '_FAST', name)
        else:
            self.emit(prefix + '_NAME', name)

    # The set_lineno() function and the explicit emit() calls for
    # SET_LINENO below are only used to generate the line number table.
    # As of Python 2.3, the interpreter does not have a SET_LINENO
    # instruction.  pyassem treats SET_LINENO opcodes as a special case.

    def set_lineno(self, node, force=False):
        """Emit SET_LINENO if necessary.

        The instruction is considered necessary if the node has a
        lineno attribute and it is different than the last lineno
        emitted.

        Returns true if SET_LINENO was emitted.

        There are no rules for when an AST node should have a lineno
        attribute.  The transformer and AST code need to be reviewed
        and a consistent policy implemented and documented.  Until
        then, this method works around missing line numbers.
        """
        lineno = getattr(node, 'lineno', None)
        if lineno is not None and (lineno != self.last_lineno
                                   or force):
            self.emit('SET_LINENO', lineno)
            self.last_lineno = lineno
            return True
        return False

    def skip_docstring(self, body):
        """Given list of statements, representing body of a function, class,
        or module, skip docstring, if any.
        """
        if isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Str):
            return body[1:]
        return body

    # The first few visitor methods handle nodes that generator new
    # code objects.  They use class attributes to determine what
    # specialized code generators to use.

    NameFinder = LocalNameFinder
    FunctionGen = None
    ClassGen = None

    def visitModule(self, node):
        self.scopes = self.parseSymbols(node)
        self.scope = self.scopes[node]
        self.emit('SET_LINENO', 0)
        doc = ast.get_docstring(node)
        if doc:
            self.set_lineno(node.body[0])
            self.emit('LOAD_CONST', doc)
            self.storeName('__doc__')
        lnf = walk(node.body, self.NameFinder(), verbose=0)
        self.locals.push(lnf.getLocals())
        self.visit(self.skip_docstring(node.body))
        self.emit('LOAD_CONST', None)
        self.emit('RETURN_VALUE')

    def visitExpression(self, node):
        self.set_lineno(node)
        self.scopes = self.parseSymbols(node)
        self.scope = self.scopes[node]
        self.visit(node.body)
        self.emit('RETURN_VALUE')

    def visitFunctionDef(self, node):
        self._visitFuncOrLambda(node, isLambda=0)
        # Handled by AbstractFunctionCode?
        #if node.doc:
        #    self.setDocstring(node.doc)
        self.storeName(node.name)

    def visitLambda(self, node):
        self._visitFuncOrLambda(node, isLambda=1)

    def _visitFuncOrLambda(self, node, isLambda=0):
        if not isLambda and node.decorator_list:
            for decorator in node.decorator_list:
                self.visit(decorator)
            ndecorators = len(node.decorator_list)
        else:
            ndecorators = 0

        gen = self.FunctionGen(node, self.scopes, isLambda,
                               self.class_name, self.get_module())
        body = node.body
        if not isLambda:
            body = self.skip_docstring(body)
        walk(body, gen)
        gen.finish()
        self.set_lineno(node)
        for default in node.args.defaults:
            self.visit(default)
        self._makeClosure(gen, len(node.args.defaults))
        for i in range(ndecorators):
            self.emit('CALL_FUNCTION', 1)

    def visitClassDef(self, node):
        gen = self.ClassGen(node, self.scopes,
                            self.get_module())
        walk(self.skip_docstring(node.body), gen)
        gen.finish()
        self.set_lineno(node)
        self.emit('LOAD_BUILD_CLASS')
        self._makeClosure(gen, 0)
        self.emit('LOAD_CONST', node.name)
        args = 2
        for base in node.bases:
            self.visit(base)
            args += 1
        self.emit('CALL_FUNCTION', args)
        self.storeName(node.name)

    # The rest are standard visitor methods

    # The next few implement control-flow statements

    def visitIf(self, node):
        test = node.test
        if is_constant_false(test):
            # XXX will need to check generator stuff here
            return
        end = self.newBlock()
        self.set_lineno(test)
        self.visit(test)
        orelse = None
        if node.orelse:
            orelse = self.newBlock()
        self.emit('POP_JUMP_IF_FALSE', orelse or end)
        self.nextBlock()
        self.visit(node.body)
        if node.orelse:
            self.emit('JUMP_FORWARD', end)
            self.startBlock(orelse)
            self.visit(node.orelse)
        self.nextBlock(end)

    def visitWhile(self, node):
        self.set_lineno(node)

        loop = self.newBlock()
        else_ = self.newBlock()

        after = self.newBlock()
        self.emit('SETUP_LOOP', after)

        self.nextBlock(loop)
        self.setups.push((LOOP, loop))

        self.set_lineno(node, force=True)
        if not is_constant_true(node.test):
            self.visit(node.test)
            self.emit('POP_JUMP_IF_FALSE', else_ or after)

        self.nextBlock()
        self.visit(node.body)
        self.emit('JUMP_ABSOLUTE', loop)

        if not is_constant_true(node.test):  # TODO: Workaround for weird block linking implementation
            self.startBlock(else_ or after) # or just the POPs if not else clause
        self.emit('POP_BLOCK')
        self.setups.pop()
        if node.orelse:
            self.visit(node.orelse)
        self.nextBlock(after)

    def visitFor(self, node):
        start = self.newBlock()
        anchor = self.newBlock()
        after = self.newBlock()
        self.setups.push((LOOP, start))

        self.set_lineno(node)
        self.emit('SETUP_LOOP', after)
        self.visit(node.iter)
        self.emit('GET_ITER')

        self.nextBlock(start)
        self.set_lineno(node, force=1)
        self.emit('FOR_ITER', anchor)
        self.visit(node.target)
        self.visit(node.body)
        self.emit('JUMP_ABSOLUTE', start)
        self.nextBlock(anchor)
        self.emit('POP_BLOCK')
        self.setups.pop()
        if node.orelse:
            self.visit(node.orelse)
        self.nextBlock(after)

    def visitBreak(self, node):
        if not self.setups:
            raise SyntaxError("'break' outside loop (%s, %d)" % \
                  (node.filename, node.lineno))
        self.set_lineno(node)
        self.emit('BREAK_LOOP')

    def visitContinue(self, node):
        if not self.setups:
            raise SyntaxError("'continue' outside loop (%s, %d)" % \
                  (node.filename, node.lineno))
        kind, block = self.setups.top()
        if kind == LOOP:
            self.set_lineno(node)
            self.emit('JUMP_ABSOLUTE', block)
            self.nextBlock()
        elif kind == EXCEPT or kind == TRY_FINALLY:
            self.set_lineno(node)
            # find the block that starts the loop
            top = len(self.setups)
            while top > 0:
                top = top - 1
                kind, loop_block = self.setups[top]
                if kind == LOOP:
                    break
            if kind != LOOP:
                raise SyntaxError("'continue' outside loop (%s, %d)" % \
                      (node.filename, node.lineno))
            self.emit('CONTINUE_LOOP', loop_block)
            self.nextBlock()
        elif kind == END_FINALLY:
            msg = "'continue' not allowed inside 'finally' clause (%s, %d)"
            raise SyntaxError(msg % (node.filename, node.lineno))

    def visitTest(self, node, jump):
        end = self.newBlock()
        for child in node.values[:-1]:
            self.visit(child)
            self.emit(jump, end)
            self.nextBlock()
        self.visit(node.values[-1])
        self.nextBlock(end)

    _boolop_opcode = {
        ast.And: "JUMP_IF_FALSE_OR_POP",
        ast.Or: "JUMP_IF_TRUE_OR_POP",
    }

    def visitBoolOp(self, node):
        opcode = self._boolop_opcode[type(node.op)]
        self.visitTest(node, opcode)

    _cmp_opcode = {
        ast.Eq: "==",
        ast.NotEq: "!=",
        ast.Lt: "<",
        ast.LtE: "<=",
        ast.Gt: ">",
        ast.GtE: ">=",
        ast.Is: "is",
        ast.IsNot: "is not",
        ast.In: "in",
        ast.NotIn: "not in",
    }

    def visitIfExp(self, node):
        endblock = self.newBlock()
        elseblock = self.newBlock()
        self.visit(node.test)
        self.emit('POP_JUMP_IF_FALSE', elseblock)
        self.visit(node.body)
        self.emit('JUMP_FORWARD', endblock)
        self.nextBlock(elseblock)
        self.visit(node.orelse)
        self.nextBlock(endblock)

    def visitCompare(self, node):
        self.visit(node.left)
        cleanup = self.newBlock()
        for op, code in node.ops[:-1]:
            self.visit(code)
            self.emit('DUP_TOP')
            self.emit('ROT_THREE')
            self.emit('COMPARE_OP', op)
            self.emit('JUMP_IF_FALSE_OR_POP', cleanup)
            self.nextBlock()
        # now do the last comparison
        if node.ops:
            op = node.ops[-1]
            code = node.comparators[-1]
            self.visit(code)
            self.emit('COMPARE_OP', self._cmp_opcode[type(op)])
        if len(node.ops) > 1:
            end = self.newBlock()
            self.emit('JUMP_FORWARD', end)
            self.startBlock(cleanup)
            self.emit('ROT_TWO')
            self.emit('POP_TOP')
            self.nextBlock(end)

    def _makeClosure(self, gen, args):
        # Construct qualname prefix
        prefix = ""
        parent = gen.scope.parent
        while not isinstance(parent, symbols.ModuleScope):
            if isinstance(parent, symbols.FunctionScope):
                prefix = parent.name + ".<locals>." + prefix
            else:
                prefix = parent.name + "." + prefix
            parent = parent.parent

        frees = gen.scope.get_free_vars()
        if frees:
            for name in frees:
                self.emit('LOAD_CLOSURE', name)
            self.emit('BUILD_TUPLE', len(frees))
            self.emit('LOAD_CONST', gen)
            self.emit('LOAD_CONST', prefix + gen.name)  # py3 qualname
            self.emit('MAKE_CLOSURE', args)
        else:
            self.emit('LOAD_CONST', gen)
            self.emit('LOAD_CONST', prefix + gen.name)  # py3 qualname
            self.emit('MAKE_FUNCTION', args)

    def wrap_comprehension(self, node, nested_scope):
        if isinstance(node, ast.GeneratorExp):
            inner = CompInner(
                node, nested_scope, None,
                [node.elt], ["YIELD_VALUE", "POP_TOP"]
            )
            inner_name = "<genexpr>"
        elif isinstance(node, ast.SetComp):
            inner = CompInner(
                node, nested_scope, ("BUILD_SET", 0),
                [node.elt], [("SET_ADD", len(node.generators) + 1)]
            )
            inner_name = "<setcomp>"
        elif isinstance(node, ast.ListComp):
            inner = CompInner(
                node, nested_scope, ("BUILD_LIST", 0),
                [node.elt], [("LIST_APPEND", len(node.generators) + 1)]
            )
            inner_name = "<listcomp>"
        elif isinstance(node, ast.DictComp):
            inner = CompInner(
                node, nested_scope, ("BUILD_MAP", 0),
                [node.value, node.key], [("MAP_ADD", len(node.generators) + 1)]
            )
            inner_name = "<dictcomp>"
        else:
            assert 0
        return inner, inner_name

    def visitNestedComp(self, node):
        # Make comprehension node to also look like function node
        class Holder: pass
        node.args = Holder()
        arg1 = Holder()
        arg1.arg = ".0"
        node.args.args = [arg1]
        node.args.vararg = None
        node.args.kwarg = None
        node.body = []

        inner, inner_name = self.wrap_comprehension(node, nested_scope=True)

        gen = GenExprCodeGenerator(node, self.scopes, self.class_name,
                                   self.get_module(), inner_name)
        walk(inner, gen)
        gen.finish()
        self.set_lineno(node)
        self._makeClosure(gen, 0)
        # precomputation of outmost iterable
        self.visit(node.generators[0].iter)
        self.emit('GET_ITER')
        self.emit('CALL_FUNCTION', 1)

    def visitInlineComp(self, node):
        inner, _ = self.wrap_comprehension(node, nested_scope=False)
        self.visit(inner)

    def visitGenericComp(self, node):
        if config.COMPREHENSION_SCOPE:
            return self.visitNestedComp(node)
        else:
            return self.visitInlineComp(node)

    # Genereator expression should be always compiled with nested scope
    # to follow generator semantics.
    visitGeneratorExp = visitNestedComp
    # Other comprehensions can be configured inline or nested-scope.
    visitSetComp = visitGenericComp
    visitListComp = visitGenericComp
    visitDictComp = visitGenericComp

    def visitcomprehension(self, node, is_outmost):
        start = self.newBlock("comp_start")
        anchor = self.newBlock("comp_anchor")
        # TODO: end is not used
        end = self.newBlock("comp_end")

        # SETUP_LOOP isn't needed because(?) break/continue are
        # not supported in comprehensions
        #self.setups.push((LOOP, start))
        #self.emit('SETUP_LOOP', end)

        if is_outmost:
            self.loadName('.0')
        else:
            self.visit(node.iter)
            self.emit('GET_ITER')

        self.nextBlock(start)
        self.set_lineno(node, force=True)
        self.emit('FOR_ITER', anchor)
        self.nextBlock()
        self.visit(node.target)
        return start, anchor, end

    def visitCompInner(self, node):
        self.set_lineno(node)
        if node.init_inst:
            self.emit(*node.init_inst)

        stack = []
        is_outmost = node.nested_scope
        for for_ in node.generators:
            start, anchor, end = self.visit(for_, is_outmost)
            is_outmost = False
            cont = None
            for if_ in for_.ifs:
                if cont is None:
                    cont = self.newBlock()
                self._visitCompIf(if_, cont)
            stack.insert(0, (start, cont, anchor, end))

        #self.visit(node.elt)
        for elt in node.elt_nodes:
            self.visit(elt)
        #self.emit('YIELD_VALUE')
        #self.emit('POP_TOP')
        for inst in node.elt_insts:
            if isinstance(inst, str):
                self.emit(inst)
            else:
                self.emit(*inst)

        for start, cont, anchor, end in stack:
            if cont:
                self.nextBlock(cont)
            self.emit('JUMP_ABSOLUTE', start)
            self.startBlock(anchor)

        if isinstance(node.obj, ast.GeneratorExp):
            self.emit('LOAD_CONST', None)

    def _visitCompIf(self, node, branch):
        self.set_lineno(node, force=True)
        self.visit(node)
        self.emit('POP_JUMP_IF_FALSE', branch)
        self.newBlock()

    # exception related

    def visitAssert(self, node):
        # XXX would be interesting to implement this via a
        # transformation of the AST before this stage
        if __debug__:
            end = self.newBlock()
            self.set_lineno(node)
            # XXX AssertionError appears to be special case -- it is always
            # loaded as a global even if there is a local name.  I guess this
            # is a sort of renaming op.
            self.nextBlock()
            self.visit(node.test)
            self.emit('POP_JUMP_IF_TRUE', end)
            self.nextBlock()
            self.emit('LOAD_GLOBAL', 'AssertionError')
            if node.msg:
                self.visit(node.msg)
                self.emit('CALL_FUNCTION', 1)
                self.emit('RAISE_VARARGS', 1)
            else:
                self.emit('RAISE_VARARGS', 1)
            self.nextBlock(end)

    def visitRaise(self, node):
        self.set_lineno(node)
        n = 0
        if node.exc:
            self.visit(node.exc)
            n = n + 1
        self.emit('RAISE_VARARGS', n)

    def visitTry(self, node):
        if node.finalbody and not node.handlers:
            self.visitTryFinally(node)
            return
        if not node.finalbody and node.handlers:
            self.visitTryExcept(node)
            return

        # Split into 2 statements, try-except wrapped with try-finally
        try_ex = ast.Try(body=node.body, handlers=node.handlers, orelse=node.orelse, finalbody=[])
        node.body = try_ex
        node.handlers = []
        node.orelse = []
        self.visitTryFinally(node)

    def visitTryExcept(self, node):
        body = self.newBlock()
        handlers = self.newBlock()
        end = self.newBlock()
        if node.orelse:
            lElse = self.newBlock()
        else:
            lElse = end
        self.set_lineno(node)
        self.emit('SETUP_EXCEPT', handlers)
        self.nextBlock(body)
        self.setups.push((EXCEPT, body))
        self.visit(node.body)
        self.emit('POP_BLOCK')
        self.setups.pop()
        self.emit('JUMP_FORWARD', lElse)
        self.startBlock(handlers)

        last = len(node.handlers) - 1
        for i in range(len(node.handlers)):
            handler = node.handlers[i]
            expr = handler.type
            target = handler.name
            body = handler.body
            self.set_lineno(expr)
            if expr:
                self.emit('DUP_TOP')
                self.visit(expr)
                self.emit('COMPARE_OP', 'exception match')
                next = self.newBlock()
                self.emit('POP_JUMP_IF_FALSE', next)
                self.nextBlock()
            self.emit('POP_TOP')
            if target:
                self.visit(ast.Name(id=target, ctx=ast.Store()))
            else:
                self.emit('POP_TOP')
            self.emit('POP_TOP')

            if target:
                protected = ast.Try(
                    body=body, handlers=[], orelse=[],
                    finalbody=[
                        ast.Assign(targets=[ast.Name(id=target, ctx=ast.Store())], value=ast.NameConstant(value=None)),
                        ast.Delete(ast.Name(id=target, ctx=ast.Del())),
                    ]
                )
                self.visitTryFinally(protected, except_protect=True)
            else:
                self.visit(body)
                self.emit('POP_EXCEPT')

            self.emit('JUMP_FORWARD', end)
            if expr:
                self.nextBlock(next)
            else:
                self.nextBlock()
        self.emit('END_FINALLY')
        if node.orelse:
            self.nextBlock(lElse)
            self.visit(node.orelse)
        self.nextBlock(end)

    def visitTryFinally(self, node, except_protect=False):
        body = self.newBlock()
        final = self.newBlock()
        self.set_lineno(node)
        self.emit('SETUP_FINALLY', final)
        self.nextBlock(body)
        self.setups.push((TRY_FINALLY, body))
        self.visit(node.body)
        self.emit('POP_BLOCK')
        self.setups.pop()
        if except_protect:
            self.emit('POP_EXCEPT')
        self.emit('LOAD_CONST', None)
        self.nextBlock(final)
        self.setups.push((END_FINALLY, final))
        self.visit(node.finalbody)
        self.emit('END_FINALLY')
        self.setups.pop()

    __with_count = 0

    def visitWith(self, node):
        body = self.newBlock()
        stack = []
        for withitem in node.items:
            final = self.newBlock()
            stack.append(final)
            self.__with_count += 1
            valuevar = "_[%d]" % self.__with_count
            self.set_lineno(node)
            self.visit(withitem.context_expr)

            py2 = 0

            if py2:
                self.emit('DUP_TOP')
                self.emit('LOAD_ATTR', '__exit__')
                self.emit('ROT_TWO')
                self.emit('LOAD_ATTR', '__enter__')
                self.emit('CALL_FUNCTION', 0)
            else:
                self.emit('SETUP_WITH', final)

            if withitem.optional_vars is None:
                self.emit('POP_TOP')
            else:
                if py2:
                    self._implicitNameOp('STORE', valuevar)
                else:
                    self.visit(withitem.optional_vars)

            if py2:
                self.emit('SETUP_FINALLY', final)

            self.setups.push((TRY_FINALLY, body))

            if py2 and withitem.optional_vars is not None:
                self._implicitNameOp('LOAD', valuevar)
                self._implicitNameOp('DELETE', valuevar)
                self.visit(withitem.optional_vars)

        self.nextBlock(body)
        self.visit(node.body)

        while stack:
            final = stack.pop()
            self.emit('POP_BLOCK')
            self.setups.pop()
            self.emit('LOAD_CONST', None)
            self.nextBlock(final)
            self.setups.push((END_FINALLY, final))
            self.emit('WITH_CLEANUP_START')
            self.emit('WITH_CLEANUP_FINISH')
            self.emit('END_FINALLY')
            self.setups.pop()
            self.__with_count -= 1

    # misc

    def visitDiscard(self, node):
        self.set_lineno(node)
        self.visit(node.expr)
        self.emit('POP_TOP')

    def visitExpr(self, node):
        self.set_lineno(node)
        self.visit(node.value)
        self.emit('POP_TOP')

    def visitNum(self, node):
        self.emit('LOAD_CONST', node.n)

    def visitStr(self, node):
        self.emit('LOAD_CONST', node.s)

    def visitBytes(self, node):
        self.emit('LOAD_CONST', node.s)

    def visitNameConstant(self, node):
        self.emit('LOAD_CONST', node.value)

    def visitConst(self, node):
        self.emit('LOAD_CONST', node.value)

    def visitKeyword(self, node):
        self.emit('LOAD_CONST', node.name)
        self.visit(node.expr)

    def visitGlobal(self, node):
        # no code to generate
        pass

    def visitName(self, node):
        self.set_lineno(node)
        if isinstance(node.ctx, ast.Store):
            self.storeName(node.id)
        elif isinstance(node.ctx, ast.Del):
            self.delName(node.id)
        else:
            self.loadName(node.id)

    def visitPass(self, node):
        self.set_lineno(node)

    def visitImport(self, node):
        self.set_lineno(node)
        level = 0
        for alias in node.names:
            name = alias.name
            asname = alias.asname
            if VERSION > 1:
                self.emit('LOAD_CONST', level)
                self.emit('LOAD_CONST', None)
            self.emit('IMPORT_NAME', name)
            mod = name.split(".")[0]
            if asname:
                self._resolveDots(name)
                self.storeName(asname)
            else:
                self.storeName(mod)

    def visitImportFrom(self, node):
        self.set_lineno(node)
        level = node.level
        fromlist = tuple(alias.name for alias in node.names)
        if VERSION > 1:
            self.emit('LOAD_CONST', level)
            self.emit('LOAD_CONST', fromlist)
        self.emit('IMPORT_NAME', node.module)
        for alias in node.names:
            name = alias.name
            asname = alias.asname
            if VERSION > 1:
                if name == '*':
                    self.namespace = 0
                    self.emit('IMPORT_STAR')
                    # There can only be one name w/ from ... import *
                    assert len(node.names) == 1
                    return
                else:
                    self.emit('IMPORT_FROM', name)
                    self._resolveDots(name)
                    self.storeName(asname or name)
            else:
                self.emit('IMPORT_FROM', name)
        self.emit('POP_TOP')

    def _resolveDots(self, name):
        elts = name.split(".")
        if len(elts) == 1:
            return
        for elt in elts[1:]:
            self.emit('LOAD_ATTR', elt)

    def visitAttribute(self, node):
        self.visit(node.value)
        if isinstance(node.ctx, ast.Store):
            self.emit('STORE_ATTR', self.mangle(node.attr))
        elif isinstance(node.ctx, ast.Del):
            self.emit('DELETE_ATTR', self.mangle(node.attr))
        else:
            self.emit('LOAD_ATTR', self.mangle(node.attr))

    # next five implement assignments

    def visitAssign(self, node):
        self.set_lineno(node)
        self.visit(node.value)
        dups = len(node.targets) - 1
        for i in range(len(node.targets)):
            elt = node.targets[i]
            if i < dups:
                self.emit('DUP_TOP')
            if isinstance(elt, ast.AST):
                self.visit(elt)

    def visitAssName(self, node):
        if node.flags == 'OP_ASSIGN':
            self.storeName(node.name)
        elif node.flags == 'OP_DELETE':
            self.set_lineno(node)
            self.delName(node.name)
        else:
            print("oops", node.flags)
            assert 0

    def visitAssAttr(self, node):
        self.visit(node.expr)
        if node.flags == 'OP_ASSIGN':
            self.emit('STORE_ATTR', self.mangle(node.attrname))
        elif node.flags == 'OP_DELETE':
            self.emit('DELETE_ATTR', self.mangle(node.attrname))
        else:
            print("warning: unexpected flags:", node.flags)
            print(node)
            assert 0

    def _visitAssSequence(self, node, op='UNPACK_SEQUENCE'):
        if findOp(node) != 'OP_DELETE':
            self.emit(op, len(node.nodes))
        for child in node.nodes:
            self.visit(child)

    if VERSION > 1:
        visitAssTuple = _visitAssSequence
        visitAssList = _visitAssSequence
    else:
        def visitAssTuple(self, node):
            self._visitAssSequence(node, 'UNPACK_TUPLE')

        def visitAssList(self, node):
            self._visitAssSequence(node, 'UNPACK_LIST')

    # augmented assignment

    def visitAugAssign(self, node):
        self.set_lineno(node)
        aug_node = wrap_aug(node.target)
        self.visit(aug_node, "load")
        self.visit(node.value)
        self.emit(self._augmented_opcode[type(node.op)])
        self.visit(aug_node, "store")

    _augmented_opcode = {
        ast.Add: 'INPLACE_ADD',
        ast.Sub: 'INPLACE_SUBTRACT',
        ast.Mult: 'INPLACE_MULTIPLY',
        ast.MatMult: 'INPLACE_MATRIX_MULTIPLY',
        ast.Div: 'INPLACE_TRUE_DIVIDE',
        ast.FloorDiv: 'INPLACE_FLOOR_DIVIDE',
        ast.Mod: 'INPLACE_MODULO',
        ast.Pow: 'INPLACE_POWER',
        ast.RShift: 'INPLACE_RSHIFT',
        ast.LShift: 'INPLACE_LSHIFT',
        ast.BitAnd: 'INPLACE_AND',
        ast.BitXor: 'INPLACE_XOR',
        ast.BitOr: 'INPLACE_OR',
        }

    def visitAugName(self, node, mode):
        if mode == "load":
            self.loadName(node.id)
        elif mode == "store":
            self.storeName(node.id)

    def visitAugAttribute(self, node, mode):
        if mode == "load":
            self.visit(node.value)
            self.emit('DUP_TOP')
            self.emit('LOAD_ATTR', self.mangle(node.attr))
        elif mode == "store":
            self.emit('ROT_TWO')
            self.emit('STORE_ATTR', self.mangle(node.attr))

    def visitAugSubscript(self, node, mode):
        if mode == "load":
            self.visitSubscript(node, 1)
        elif mode == "store":
            self.emit('ROT_THREE')
            self.emit('STORE_SUBSCR')

    def visitExec(self, node):
        self.visit(node.expr)
        if node.locals is None:
            self.emit('LOAD_CONST', None)
        else:
            self.visit(node.locals)
        if node.globals is None:
            self.emit('DUP_TOP')
        else:
            self.visit(node.globals)
        self.emit('EXEC_STMT')

    def visitCall(self, node):
        pos = 0
        kw = 0
        self.set_lineno(node)
        self.visit(node.func)
        star_args = None
        dstar_args = None
        for arg in node.args:
            if isinstance(arg, ast.Starred):
                star_args = arg
            else:
                self.visit(arg)
                pos = pos + 1

        for kwarg in node.keywords:
            if kwarg.arg is None:
                dstar_args = kwarg.value
            else:
                self.emit('LOAD_CONST', kwarg.arg)
                self.visit(kwarg.value)
                kw = kw + 1

        if star_args is not None:
            self.visit(star_args)
        if dstar_args is not None:
            self.visit(dstar_args)
        have_star = star_args is not None
        have_dstar = dstar_args is not None
        opcode = callfunc_opcode_info[have_star, have_dstar]
        self.emit(opcode, kw << 8 | pos)

    def visitPrint(self, node, newline=0):
        self.set_lineno(node)
        if node.dest:
            self.visit(node.dest)
        for child in node.nodes:
            if node.dest:
                self.emit('DUP_TOP')
            self.visit(child)
            if node.dest:
                self.emit('ROT_TWO')
                self.emit('PRINT_ITEM_TO')
            else:
                self.emit('PRINT_ITEM')
        if node.dest and not newline:
            self.emit('POP_TOP')

    def visitPrintnl(self, node):
        self.visitPrint(node, newline=1)
        if node.dest:
            self.emit('PRINT_NEWLINE_TO')
        else:
            self.emit('PRINT_NEWLINE')

    def visitReturn(self, node):
        self.set_lineno(node)
        if node.value:
            self.visit(node.value)
        else:
            self.emit('LOAD_CONST', None)
        self.emit('RETURN_VALUE')

    def visitYield(self, node):
        self.set_lineno(node)
        if node.value:
            self.visit(node.value)
        else:
            self.emit('LOAD_CONST', None)
        self.emit('YIELD_VALUE')

    # slice and subscript stuff

    def visitSubscript(self, node, aug_flag=None):
        self.visit(node.value)
        self.visit(node.slice)

        if isinstance(node.ctx, ast.Load):
            self.emit('BINARY_SUBSCR')
        elif isinstance(node.ctx, ast.Store):
            if aug_flag:
                self.emit('DUP_TOP_TWO')
                self.emit('BINARY_SUBSCR')
            else:
                self.emit('STORE_SUBSCR')
        elif isinstance(node.ctx, ast.Del):
            self.emit('DELETE_SUBSCR')
        else:
            assert 0

    # binary ops

    def binaryOp(self, node, op):
        self.visit(node.left)
        self.visit(node.right)
        self.emit(op)

    _binary_opcode = {
        ast.Add: "BINARY_ADD",
        ast.Sub: "BINARY_SUBTRACT",
        ast.Mult: "BINARY_MULTIPLY",
        ast.MatMult: "BINARY_MATRIX_MULTIPLY",
        ast.Div: "BINARY_TRUE_DIVIDE",
        ast.FloorDiv: "BINARY_FLOOR_DIVIDE",
        ast.Mod: "BINARY_MODULO",
        ast.Pow: "BINARY_POWER",
        ast.LShift: "BINARY_LSHIFT",
        ast.RShift: "BINARY_RSHIFT",
        ast.BitOr: "BINARY_OR",
        ast.BitXor: "BINARY_XOR",
        ast.BitAnd: "BINARY_AND",
    }

    def visitBinOp(self, node):
        self.visit(node.left)
        self.visit(node.right)
        op = self._binary_opcode[type(node.op)]
        self.emit(op)

    # unary ops

    def unaryOp(self, node, op):
        self.visit(node.operand)
        self.emit(op)

    _unary_opcode = {
        ast.Invert: "UNARY_INVERT",
        ast.USub: "UNARY_NEGATIVE",
        ast.UAdd: "UNARY_POSITIVE",
        ast.Not: "UNARY_NOT",
    }

    def visitUnaryOp(self, node):
        self.unaryOp(node, self._unary_opcode[type(node.op)])

    def visitBackquote(self, node):
        return self.unaryOp(node, 'UNARY_CONVERT')

    # object constructors

    def visitEllipsis(self, node):
        self.emit('LOAD_CONST', Ellipsis)

    def visitTuple(self, node):
        self.set_lineno(node)
        if isinstance(node.ctx, ast.Store):
            self.emit('UNPACK_SEQUENCE', len(node.elts))
        for elt in node.elts:
            self.visit(elt)
        if isinstance(node.ctx, ast.Load):
            self.emit('BUILD_TUPLE', len(node.elts))

    def visitList(self, node):
        self.set_lineno(node)
        for elt in node.elts:
            self.visit(elt)
        self.emit('BUILD_LIST', len(node.elts))

    def visitSet(self, node):
        self.set_lineno(node)
        for elt in node.elts:
            self.visit(elt)
        self.emit('BUILD_SET', len(node.elts))

    def visitSlice(self, node):
        num = 2
        if node.lower:
            self.visit(node.lower)
        else:
            self.emit('LOAD_CONST', None)
        if node.upper:
            self.visit(node.upper)
        else:
            self.emit('LOAD_CONST', None)
        if node.step:
            self.visit(node.step)
            num += 1
        self.emit('BUILD_SLICE', num)

    # Create dict item by item. Saves interp stack size at the expense
    # of bytecode size/speed.
    def visitDict_by_one(self, node):
        self.set_lineno(node)
        self.emit('BUILD_MAP', 0)
        for k, v in zip(node.keys, node.values):
            self.emit('DUP_TOP')
            self.visit(k)
            self.visit(v)
            self.emit('ROT_THREE')
            self.emit('STORE_SUBSCR')

    def visitDict(self, node):
        self.set_lineno(node)
        for k, v in zip(node.keys, node.values):
            self.visit(k)
            self.visit(v)
        self.emit('BUILD_MAP', len(node.keys))

class NestedScopeMixin:
    """Defines initClass() for nested scoping (Python 2.2-compatible)"""
    def initClass(self):
        self.__class__.NameFinder = LocalNameFinder
        self.__class__.FunctionGen = FunctionCodeGenerator
        self.__class__.ClassGen = ClassCodeGenerator

class ModuleCodeGenerator(NestedScopeMixin, CodeGenerator):
    __super_init = CodeGenerator.__init__

    scopes = None

    def __init__(self, tree):
        self.filename = tree.filename
        self.graph = pyassem.PyFlowGraph("<module>", tree.filename)
        self.futures = future.find_futures(tree)
        self.__super_init()
        walk(tree, self)

    def get_module(self):
        return self

class ExpressionCodeGenerator(NestedScopeMixin, CodeGenerator):
    __super_init = CodeGenerator.__init__

    scopes = None
    futures = ()

    def __init__(self, tree):
        self.graph = pyassem.PyFlowGraph("<expression>", tree.filename)
        self.__super_init()
        walk(tree, self)

    def get_module(self):
        return self

class InteractiveCodeGenerator(NestedScopeMixin, CodeGenerator):

    __super_init = CodeGenerator.__init__

    scopes = None
    futures = ()

    def __init__(self, tree):
        self.graph = pyassem.PyFlowGraph("<interactive>", tree.filename)
        self.__super_init()
        self.set_lineno(tree)
        walk(tree, self)
        self.emit('RETURN_VALUE')

    def get_module(self):
        return self

    def visitDiscard(self, node):
        # XXX Discard means it's an expression.  Perhaps this is a bad
        # name.
        self.visit(node.expr)
        self.emit('PRINT_EXPR')

class AbstractFunctionCode:
    optimized = 1
    lambdaCount = 0

    def __init__(self, func, scopes, isLambda, class_name, mod, lambda_name="<lambda>"):
        self.class_name = class_name
        self.module = mod
        if isLambda:
            klass = FunctionCodeGenerator
            name = lambda_name
            klass.lambdaCount = klass.lambdaCount + 1
        else:
            name = func.name

        self.name = name

        args = [elt.arg for elt in func.args.args]

        if func.args.vararg:
            args.append(func.args.vararg.arg)
        if func.args.kwarg:
            args.append(func.args.kwarg.arg)
        filename = mod.filename
        self.graph = pyassem.PyFlowGraph(name, filename, args,
                                         optimized=1)
        self.isLambda = isLambda
        self.super_init()

        if not isLambda:
            doc = ast.get_docstring(func)
            if doc:
                self.setDocstring(doc)

        lnf = walk(func.body, self.NameFinder(args), verbose=0)
        self.locals.push(lnf.getLocals())
        if func.args.vararg:
            self.graph.setFlag(CO_VARARGS)
        if func.args.kwarg:
            self.graph.setFlag(CO_VARKEYWORDS)
        self.set_lineno(func)

    def get_module(self):
        return self.module

    def finish(self):
        self.graph.startExitBlock()
        if not self.isLambda:
            self.emit('LOAD_CONST', None)
        self.emit('RETURN_VALUE')

    def unpackSequence(self, tup):
        if VERSION > 1:
            self.emit('UNPACK_SEQUENCE', len(tup))
        else:
            self.emit('UNPACK_TUPLE', len(tup))
        for elt in tup:
            if isinstance(elt, tuple):
                self.unpackSequence(elt)
            else:
                self._nameOp('STORE', elt)

    unpackTuple = unpackSequence

class FunctionCodeGenerator(NestedScopeMixin, AbstractFunctionCode,
                            CodeGenerator):
    super_init = CodeGenerator.__init__ # call be other init
    scopes = None

    __super_init = AbstractFunctionCode.__init__

    def __init__(self, func, scopes, isLambda, class_name, mod):
        self.scopes = scopes
        self.scope = scopes[func]
        self.__super_init(func, scopes, isLambda, class_name, mod)
        self.graph.setFreeVars(self.scope.get_free_vars())
        self.graph.setCellVars(self.scope.get_cell_vars())
        if self.scope.generator is not None:
            self.graph.setFlag(CO_GENERATOR)

class GenExprCodeGenerator(NestedScopeMixin, AbstractFunctionCode,
                           CodeGenerator):
    super_init = CodeGenerator.__init__ # call be other init
    scopes = None

    __super_init = AbstractFunctionCode.__init__

    def __init__(self, gexp, scopes, class_name, mod, inner_name):
        self.scopes = scopes
        self.scope = scopes[gexp]
        self.__super_init(gexp, scopes, 1, class_name, mod, lambda_name=inner_name)
        self.graph.setFreeVars(self.scope.get_free_vars())
        self.graph.setCellVars(self.scope.get_cell_vars())
        self.graph.setFlag(CO_GENERATOR)

class AbstractClassCode:

    def __init__(self, klass, scopes, module):
        self.class_name = klass.name
        self.module = module
        self.name = klass.name
        filename = module.filename
        self.graph = pyassem.PyFlowGraph(klass.name, filename,
                                           optimized=0, klass=1)
        self.super_init()
        lnf = walk(klass.body, self.NameFinder(), verbose=0)
        self.locals.push(lnf.getLocals())
        self.graph.setFlag(CO_NEWLOCALS)
        doc = ast.get_docstring(klass)
        if doc:
            self.setDocstring(doc)

    def get_module(self):
        return self.module

    def finish(self):
        self.graph.startExitBlock()
        self.emit('LOAD_CONST', None)
        self.emit('RETURN_VALUE')

class ClassCodeGenerator(NestedScopeMixin, AbstractClassCode, CodeGenerator):
    super_init = CodeGenerator.__init__
    scopes = None

    __super_init = AbstractClassCode.__init__

    def __init__(self, klass, scopes, module):
        self.scopes = scopes
        self.scope = scopes[klass]
        self.__super_init(klass, scopes, module)
        self.graph.setFreeVars(self.scope.get_free_vars())
        self.graph.setCellVars(self.scope.get_cell_vars())
        self.set_lineno(klass)
        self.emit("LOAD_NAME", "__name__")
        self.storeName("__module__")
        self.emit("LOAD_CONST", self.name)
        self.storeName("__qualname__")
        doc = ast.get_docstring(klass)
        if doc:
            self.set_lineno(klass.body[0])
            self.emit("LOAD_CONST", doc)
            self.storeName('__doc__')


def findOp(node):
    """Find the op (DELETE, LOAD, STORE) in an AssTuple tree"""
    v = OpFinder()
    walk(node, v, verbose=0)
    return v.op

class OpFinder:
    def __init__(self):
        self.op = None
    def visitAssName(self, node):
        if self.op is None:
            self.op = node.flags
        elif self.op != node.flags:
            raise ValueError("mixed ops in stmt")
    visitAssAttr = visitAssName
    visitSubscript = visitAssName

class Delegator:
    """Base class to support delegation for augmented assignment nodes

    To generator code for augmented assignments, we use the following
    wrapper classes.  In visitAugAssign, the left-hand expression node
    is visited twice.  The first time the visit uses the normal method
    for that node .  The second time the visit uses a different method
    that generates the appropriate code to perform the assignment.
    These delegator classes wrap the original AST nodes in order to
    support the variant visit methods.
    """
    def __init__(self, obj):
        self.obj = obj

    def __getattr__(self, attr):
        return getattr(self.obj, attr)

class AugAttribute(Delegator):
    pass

class AugName(Delegator):
    pass

class AugSubscript(Delegator):
    pass

class CompInner(Delegator):

    def __init__(self, obj, nested_scope, init_inst, elt_nodes, elt_insts):
        Delegator.__init__(self, obj)
        self.nested_scope = nested_scope
        self.init_inst = init_inst
        self.elt_nodes = elt_nodes
        self.elt_insts = elt_insts

wrapper = {
    ast.Attribute: AugAttribute,
    ast.Name: AugName,
    ast.Subscript: AugSubscript,
}

def wrap_aug(node):
    return wrapper[node.__class__](node)

if __name__ == "__main__":
    for file in sys.argv[1:]:
        compileFile(file)
