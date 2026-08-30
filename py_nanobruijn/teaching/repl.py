from __future__ import annotations

import sys

from ..errors import CheckTimeoutError, ParseError
from ..ptr import ExprPtr
from .core import BootstrapCore
from .parser import parse_expr
from .pretty import pretty
from .reduce import reduce_steps, show_reduction

BANNER = (
    "py-nanobruijn teaching REPL\n"
    "输入表达式查看类型（等价 #check），或使用命令：#check/#reduce/#print/#env/#help/#quit\n"
    "语法：fun (x : A) => e、∀ (x : A), e、A -> B、@Const、Type、Prop"
)


class Repl:
    def __init__(self, core: BootstrapCore, timeout_secs: float = 5.0):
        self.core = core
        self.timeout_secs = float(timeout_secs)

    # ---------- 命令 ----------

    def process_line(self, line: str) -> str:
        text = line.strip()
        if not text:
            return ""
        if text.startswith("#"):
            return self._command(text)
        return self._check(text)

    def _command(self, text: str) -> str:
        parts = text[1:].split(maxsplit=1)
        cmd = parts[0]
        rest = parts[1] if len(parts) > 1 else ""
        if cmd == "help":
            return BANNER
        if cmd == "quit":
            raise EOFError()
        if cmd == "env":
            return "\n".join(self.core.constants())
        if cmd == "print":
            return self._print_const(rest)
        if cmd == "reduce":
            return self._run_reduce(rest)
        if cmd == "check":
            return self._check(rest)
        return f"unknown command #{cmd} (try #help)"

    def _check(self, text: str) -> str:
        try:
            e = parse_expr(self.core, text)
            if self._has_nat_lit(e):
                return "error: Nat 字面量的类型推断在 v1 教学核心中暂不支持（需要 Nat inductive 类型）"
            tc = self.core.make_type_checker(self.timeout_secs)
            ty = tc.infer(e, 'check')
            return f"{pretty(self.core, e)} : {pretty(self.core, ty)}"
        except (ValueError, CheckTimeoutError, ParseError) as err:
            return f"error: {err}"
        except Exception as err:  # noqa: BLE001 - REPL 顶层兜底
            return f"error: {type(err).__name__}: {err}"

    def _has_nat_lit(self, e: ExprPtr) -> bool:
        v = self.core.ctx.view_expr(e)
        tag = v.tag
        if tag == 'NatLit':
            return True
        if tag == 'App':
            return self._has_nat_lit(v.fun) or self._has_nat_lit(v.arg)
        if tag in ('Pi', 'Lambda'):
            return self._has_nat_lit(v.binder_type) or self._has_nat_lit(v.body)
        if tag == 'Let':
            return (self._has_nat_lit(v.binder_type) or
                    self._has_nat_lit(v.val) or self._has_nat_lit(v.body))
        if tag == 'Proj':
            return self._has_nat_lit(v.structure)
        return False

    def _run_reduce(self, text: str) -> str:
        try:
            e = parse_expr(self.core, text)
            tc = self.core.make_type_checker(self.timeout_secs)
            return show_reduction(self.core, reduce_steps(tc, e))
        except (ValueError, CheckTimeoutError, ParseError) as err:
            return f"error: {err}"
        except Exception as err:  # noqa: BLE001
            return f"error: {type(err).__name__}: {err}"

    def _print_const(self, text: str) -> str:
        text = text.strip()
        if not text:
            return "usage: #print <name>"
        ptr = self.core.name_to_ptr(text)
        decl = self.core.env.declars.get(ptr)
        if decl is None:
            return f"error: unknown constant {text!r}"
        from ..env import Axiom, Definition, OpaqueDecl, Theorem
        lines = [(f"{self.core.name_to_string(decl.info.name)} : "
                  f"{pretty(self.core, ExprPtr.closed(decl.info.ty))}")]
        if isinstance(decl, (Definition, Theorem, OpaqueDecl)):
            lines.append(f"  = {pretty(self.core, ExprPtr.closed(decl.value))}")
        elif isinstance(decl, Axiom):
            lines.append("  (axiom)")
        return "\n".join(lines)

    # ---------- 主循环 ----------

    def run(self, stdin=None, stdout=None) -> int:
        stdin = stdin or sys.stdin
        stdout = stdout or sys.stdout
        print(BANNER, file=stdout)
        print(f"已加载 {len(self.core.constants())} 个常量，输入 #help 查看帮助", file=stdout)
        while True:
            try:
                line = input("> ") if stdin is sys.stdin else stdin.readline()
            except EOFError:
                return 0
            if not line:
                if stdin is not sys.stdin:
                    return 0
                continue
            try:
                out = self.process_line(line)
            except EOFError:
                return 0
            if out:
                print(out, file=stdout)