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
    kind: str  # 'beta' | 'delta'


def reduce_steps(tc: TypeChecker, e: ExprPtr) -> list[ReductionStep]:
    steps: list[ReductionStep] = []
    cursor = e
    while True:
        r = tc.whnf_no_unfolding(cursor)
        unfolded = tc.unfold_def(r)
        if unfolded is not None:
            steps.append(ReductionStep(cursor, unfolded, "delta"))
            cursor = unfolded
            continue
        if r != cursor:
            steps.append(ReductionStep(cursor, r, "beta"))
            cursor = r
            continue
        break
    return steps


def show_reduction(core: BootstrapCore, steps: list[ReductionStep],
                   color: bool = False) -> str:
    lines = []
    for s in steps:
        tag = f"[{s.kind}]"
        if color:
            tag = colorize(tag, "blue" if s.kind == "beta" else "magenta")
        lines.append(f"{pretty(core, s.before, color)} => "
                     f"{pretty(core, s.after, color)}  {tag}")
    if not lines:
        return "(already in normal form)"
    return "\n".join(lines)
