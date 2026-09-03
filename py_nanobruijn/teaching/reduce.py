from __future__ import annotations

from typing import NamedTuple

from ..ptr import ExprPtr
from ..tc_whnf import TypeChecker
from .core import BootstrapCore
from .pretty import pretty
from .style import colorize


class ReductionStep(NamedTuple):
    before: ExprPtr
    after: ExprPtr
    kind: str  # 'beta' | 'delta' | 'iota'


def _head_rec_args(tc: TypeChecker, e: ExprPtr):
    """头是带规则的 RecursorDecl 且参数给到 major 位时返回 (name, levels, args)。"""
    fun, args = tc.ctx.unfold_apps(e)
    expr = tc.ctx.dag.get_expr(fun.core)
    if expr.tag != 'Const':
        return None
    rec = tc.env.get_recursor(expr.children[0])
    if rec is None or not rec.rules or len(args) <= rec.major_idx():
        return None
    return expr.children[0], expr.children[1], args


def reduce_steps(tc: TypeChecker, e: ExprPtr) -> list[ReductionStep]:
    """逐步归约，镜像 whnf 主循环的分派顺序：iota → delta → beta → 参数下降。

    头卡住但参数里有可归约子项时下探第一个可归约参数（如
    `succ (Nat.rec … one)` 的内部继续计算），保证归约链走到底。
    """
    steps: list[ReductionStep] = []
    cursor = e
    while True:
        head = _head_rec_args(tc, cursor)
        if head is not None:
            r = tc.reduce_rec(*head)
            if r is not None:
                steps.append(ReductionStep(cursor, r, "iota"))
                cursor = r
                continue
        unfolded = tc.unfold_def(cursor)
        if unfolded is not None:
            steps.append(ReductionStep(cursor, unfolded, "delta"))
            cursor = unfolded
            continue
        r = tc.whnf_no_unfolding(cursor)
        if r != cursor:
            steps.append(ReductionStep(cursor, r, "beta"))
            cursor = r
            continue
        # 头卡住（ctor/已约简常量）：下探参数；子步以完整表达式形式记录
        fun, args = tc.ctx.unfold_apps(cursor)
        descended = False
        for i, a in enumerate(args):
            sub = reduce_steps(tc, a)
            if sub:
                new_args = list(args)
                for s in sub:
                    new_args[i] = s.after
                    whole = tc.ctx.foldl_apps(fun, new_args)
                    steps.append(ReductionStep(cursor, whole, s.kind))
                    cursor = whole
                descended = True
                break
        if not descended:
            break
    return steps


def show_reduction(core: BootstrapCore, steps: list[ReductionStep],
                   color: bool = False) -> str:
    lines = []
    kind_colors = {"beta": "blue", "delta": "magenta", "iota": "cyan"}
    for s in steps:
        tag = f"[{s.kind}]"
        if color:
            tag = colorize(tag, kind_colors.get(s.kind, "blue"))
        lines.append(f"{pretty(core, s.before, color)} => "
                     f"{pretty(core, s.after, color)}  {tag}")
    if not lines:
        return "(already in normal form)"
    return "\n".join(lines)
