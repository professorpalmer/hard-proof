"""A small AST mutator for one Python function.

Each mutant changes one place of the function source. The operators:

- negate the condition of an `if`, `while`, conditional expression or `assert`,
- swap `and` and `or`,
- change a comparison operator,
- change an integer constant by one,
- replace a `return` value by `None`,
- delete one statement (replace it with `pass`),
- swap two arguments of the same call, when both are positional or both are keywords.
"""
from __future__ import annotations

import __future__ as future
import ast
import copy
import inspect
import random
import textwrap
import types

COMPARE_SWAPS = {
    ast.Eq: [ast.NotEq], ast.NotEq: [ast.Eq],
    ast.Lt: [ast.LtE, ast.Gt], ast.LtE: [ast.Lt, ast.GtE],
    ast.Gt: [ast.GtE, ast.Lt], ast.GtE: [ast.Gt, ast.LtE],
    ast.In: [ast.NotIn], ast.NotIn: [ast.In],
    ast.Is: [ast.IsNot], ast.IsNot: [ast.Is],
}
OP_TEXT = {ast.Eq: "==", ast.NotEq: "!=", ast.Lt: "<", ast.LtE: "<=", ast.Gt: ">", ast.GtE: ">=",
           ast.In: "in", ast.NotIn: "not in", ast.Is: "is", ast.IsNot: "is not"}


class Site:
    """One place to mutate: the index of a node in `ast.walk` order and an operation."""

    def __init__(self, index: int, op: str, arg=None):
        self.index = index
        self.op = op
        self.arg = arg


def short(node) -> str:
    text = ast.unparse(node).replace("\n", " ")
    return text if len(text) <= 60 else text[:57] + "..."


def function_tree(func) -> ast.FunctionDef:
    source = textwrap.dedent(inspect.getsource(func))
    tree = ast.parse(source)
    fn = tree.body[0]
    if not isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
        raise ValueError("the source is not one function definition")
    fn.decorator_list = []
    return fn


def is_docstring(parent, field: str, pos: int) -> bool:
    if field != "body" or pos != 0:
        return False
    stmt = getattr(parent, field)[0]
    return isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str)


def sites(fn: ast.FunctionDef) -> list:
    found = []
    nodes = list(ast.walk(fn))
    for idx, node in enumerate(nodes):
        if isinstance(node, (ast.If, ast.While, ast.IfExp, ast.Assert)):
            found.append(Site(idx, "negate"))
        if isinstance(node, ast.BoolOp):
            found.append(Site(idx, "boolop"))
        if isinstance(node, ast.Compare):
            for k, op in enumerate(node.ops):
                for repl in COMPARE_SWAPS.get(type(op), []):
                    found.append(Site(idx, "compare", (k, repl)))
        if isinstance(node, ast.Constant) and type(node.value) is int:
            found.append(Site(idx, "const", 1))
            found.append(Site(idx, "const", -1))
        if isinstance(node, ast.Return) and node.value is not None and not (
                isinstance(node.value, ast.Constant) and node.value.value is None):
            found.append(Site(idx, "return"))
        for field in ("body", "orelse", "finalbody"):
            stmts = getattr(node, field, None)
            if node is fn and field != "body":
                continue
            if isinstance(stmts, list) and stmts and isinstance(stmts[0], ast.stmt):
                for pos in range(len(stmts)):
                    if not is_docstring(node, field, pos) and not isinstance(stmts[pos], ast.Pass):
                        found.append(Site(idx, "delete", (field, pos)))
        if isinstance(node, ast.Call):
            for k in range(len(node.args) - 1):
                if not any(isinstance(a, ast.Starred) for a in node.args[k:k + 2]):
                    found.append(Site(idx, "swap_args", k))
            kws = [kw for kw in node.keywords if kw.arg is not None]
            for k in range(len(kws) - 1):
                found.append(Site(idx, "swap_kwargs", (kws[k].arg, kws[k + 1].arg)))
    return found


def apply(fn: ast.FunctionDef, site: Site) -> tuple:
    """Return (mutated copy, one-line description)."""
    new = copy.deepcopy(fn)
    node = list(ast.walk(new))[site.index]
    line = getattr(node, "lineno", 0) - fn.lineno + 1
    where = f"line {line}" if line > 0 else "function"
    if site.op == "negate":
        desc = f"{where}: negate the condition `{short(node.test)}`"
        node.test = ast.UnaryOp(op=ast.Not(), operand=node.test)
    elif site.op == "boolop":
        old = "and" if isinstance(node.op, ast.And) else "or"
        desc = f"{where}: `{old}` to `{'or' if old == 'and' else 'and'}` in `{short(node)}`"
        node.op = ast.Or() if isinstance(node.op, ast.And) else ast.And()
    elif site.op == "compare":
        k, repl = site.arg
        desc = f"{where}: `{OP_TEXT[type(node.ops[k])]}` to `{OP_TEXT[repl]}` in `{short(node)}`"
        node.ops[k] = repl()
    elif site.op == "const":
        desc = f"{where}: constant {node.value} to {node.value + site.arg}"
        node.value = node.value + site.arg
    elif site.op == "return":
        desc = f"{where}: `return {short(node.value)}` to `return None`"
        node.value = ast.Constant(value=None)
    elif site.op == "delete":
        field, pos = site.arg
        stmts = getattr(node, field)
        target = stmts[pos]
        tline = target.lineno - fn.lineno + 1
        desc = f"line {tline}: delete `{short(target).split(chr(10))[0]}`"
        stmts[pos] = ast.Pass()
    elif site.op == "swap_args":
        k = site.arg
        desc = f"{where}: swap arguments {k + 1} and {k + 2} in `{short(node)}`"
        node.args[k], node.args[k + 1] = node.args[k + 1], node.args[k]
    elif site.op == "swap_kwargs":
        a, b = site.arg
        kws = {kw.arg: kw for kw in node.keywords if kw.arg is not None}
        kws[a].value, kws[b].value = kws[b].value, kws[a].value
        desc = f"{where}: swap the values of `{a}` and `{b}` in `{short(node)}`"
    else:
        raise ValueError(site.op)
    ast.fix_missing_locations(new)
    return new, desc


def compile_like(fn: ast.FunctionDef, original) -> types.FunctionType:
    """Compile a function tree with the globals, defaults and closure of `original`."""
    module = ast.Module(body=[fn], type_ignores=[])
    ast.fix_missing_locations(module)
    code = compile(module, filename=f"<hardproof mutant of {original.__name__}>", mode="exec",
                   flags=future.annotations.compiler_flag, dont_inherit=True)
    scratch = dict(original.__globals__)
    exec(code, scratch)
    made = scratch[fn.name]
    if original.__closure__:
        raise ValueError("a function with a closure cannot be mutated")
    func = types.FunctionType(made.__code__, original.__globals__, original.__name__,
                              original.__defaults__, None)
    func.__kwdefaults__ = original.__kwdefaults__
    func.__module__ = original.__module__
    func.__qualname__ = original.__qualname__
    return func


def mutants(func, limit: int, seed: int) -> list:
    """Return (identity copy, list of (description, function), number of sites).

    The list has up to `limit` mutants. The identity copy is the unchanged
    source compiled the same way. The link test uses it to show that a
    recompiled function behaves as the original.
    """
    fn = function_tree(func)
    identity = compile_like(copy.deepcopy(fn), func)
    all_sites = sites(fn)
    rng = random.Random(seed)
    chosen = all_sites if len(all_sites) <= limit else rng.sample(all_sites, limit)
    chosen.sort(key=lambda s: (s.index, s.op, str(s.arg)))
    out = []
    for site in chosen:
        tree, desc = apply(fn, site)
        try:
            out.append((desc, compile_like(tree, func)))
        except (SyntaxError, ValueError, TypeError) as exc:
            out.append((desc, exc))
    return identity, out, len(all_sites)
