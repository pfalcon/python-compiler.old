import ast
import operator
from ast import Constant, Num, Str, Bytes, Ellipsis, NameConstant, copy_location

from compiler.visitor import ASTRewriter


def is_const(node):
    return isinstance(node, (Constant, Num, Str, Bytes, Ellipsis, NameConstant))


def get_const_value(node):
    if isinstance(node, (Constant, NameConstant)):
        return node.value
    elif isinstance(node, Num):
        return node.n
    elif isinstance(node, (Str, Bytes)):
        return node.s
    elif isinstance(node, Ellipsis):
        return ...

    raise TypeError("Bad constant value")


UNARY_OPS = {
    ast.Invert: operator.invert,
    ast.Not: operator.not_,
    ast.UAdd: operator.pos,
    ast.USub: operator.neg,
}
INVERSE_OPS = {
    ast.Is: ast.IsNot,
    ast.IsNot: ast.Is,
    ast.In: ast.NotIn,
    ast.NotIn: ast.In,
}


class AstOptimizer(ASTRewriter):
    def visitUnaryOp(self, node: ast.UnaryOp):
        op = self.visit(node.operand)
        if is_const(op):
            conv = UNARY_OPS[type(node.op)]
            val = get_const_value(op)
            try:
                return copy_location(Constant(conv(val)), node)
            except:
                pass
        elif (
            isinstance(node.op, ast.Not)
            and isinstance(node.operand, ast.Compare)
            and len(node.operand.ops) == 1
        ):
            cmp_op = node.operand.ops[0]
            new_op = INVERSE_OPS.get(type(cmp_op))
            if new_op is not None:
                return self.update_node(node.operand, ops=[new_op()])

        return self.update_node(node, operand=op)
