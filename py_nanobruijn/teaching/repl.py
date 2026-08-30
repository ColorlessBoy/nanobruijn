from __future__ import annotations

import sys

from ..errors import CheckTimeoutError, ParseError
from ..ptr import ExprPtr
from .core import BootstrapCore
from .parser import parse_expr
from .pretty import pretty
from .proof import ProofState
from .reduce import reduce_steps, show_reduction
from .style import color_enabled, colorize
from .tactics import AbortProof, ProofDone, run_tactic

BANNER = (
    "py-nanobruijn teaching REPL\n"
    "输入表达式查看类型（等价 #check），或使用命令："
    "#check/#reduce/#print/#prove/#env/#help/#quit\n"
    "语法：fun (x : A) => e、forall (x : A), e、A -> B、@Const、Type、Prop\n"
    "提示：∀ 可写 forall，→ 可写 ->（纯键盘友好）"
)


class _ProveSession(Exception):
    """process_line 的内部信号：进入 #prove 证明子循环（由 run() 捕获）。"""

    def __init__(self, state: ProofState):
        super().__init__("prove session")
        self.state = state


class Repl:
    def __init__(self, core: BootstrapCore, timeout_secs: float = 5.0,
                 color: bool | None = None):
        self.core = core
        self.timeout_secs = float(timeout_secs)
        self.color = color_enabled(color)

    def _c(self, text: str, color: str) -> str:
        if not self.color:
            return text
        return colorize(text, color)

    def _error(self, msg: str) -> str:
        return f"{self._c('error:', 'red')} {msg}"

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
        if cmd == "prove":
            return self._prove(rest)
        return f"unknown command #{cmd} (try #help)"

    def _check(self, text: str) -> str:
        try:
            e = parse_expr(self.core, text)
            if self._has_nat_lit(e):
                return self._error("Nat 字面量的类型推断在 v1 教学核心中暂不支持（需要 Nat inductive 类型）")
            tc = self.core.make_type_checker(self.timeout_secs)
            ty = tc.infer(e, 'check')
            return f"{pretty(self.core, e, self.color)} : {pretty(self.core, ty, self.color)}"
        except (ValueError, CheckTimeoutError, ParseError) as err:
            return self._error(str(err))
        except Exception as err:  # noqa: BLE001 - REPL 顶层兜底
            return self._error(f"{type(err).__name__}: {err}")

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
            return show_reduction(self.core, reduce_steps(tc, e), self.color)
        except (ValueError, CheckTimeoutError, ParseError) as err:
            return self._error(str(err))
        except Exception as err:  # noqa: BLE001
            return self._error(f"{type(err).__name__}: {err}")

    def _print_const(self, text: str) -> str:
        text = text.strip()
        if not text:
            return "usage: #print <name>"
        ptr = self.core.name_to_ptr(text)
        decl = self.core.env.declars.get(ptr)
        if decl is None:
            return self._error(f"unknown constant {text!r}")
        from ..env import Axiom, Definition, OpaqueDecl, Theorem
        lines = [(f"{self.core.name_to_string(decl.info.name)} : "
                  f"{pretty(self.core, ExprPtr.closed(decl.info.ty), self.color)}")]
        if isinstance(decl, (Definition, Theorem, OpaqueDecl)):
            lines.append(f"  = {pretty(self.core, ExprPtr.closed(decl.value), self.color)}")
        elif isinstance(decl, Axiom):
            lines.append(f"  {self._c('(axiom)', 'gray')}")
        return "\n".join(lines)

    def _prove(self, text: str) -> str:
        text = text.strip()
        if not text:
            return "usage: #prove <类型>"
        try:
            goal_ty = parse_expr(self.core, text)
            state = ProofState(self.core, goal_ty, self.timeout_secs, self.color)
        except (ValueError, ParseError) as err:
            return self._error(str(err))
        raise _ProveSession(state)

    # ---------- 主循环 ----------

    def run(self, stdin=None, stdout=None) -> int:
        stdin = stdin or sys.stdin
        stdout = stdout or sys.stdout
        print(BANNER, file=stdout)
        print(f"已加载 {len(self.core.constants())} 个常量，输入 #help 查看帮助", file=stdout)
        session_path = self._open_session(stdout)
        while True:
            try:
                prompt = self._c("> ", "green")
                line = input(prompt) if stdin is sys.stdin else stdin.readline()
            except EOFError:
                return 0
            if not line:
                if stdin is not sys.stdin:
                    return 0
                continue
            self._record_session(session_path, line)
            try:
                out = self.process_line(line)
            except _ProveSession as session:
                self._run_proof(session.state, stdin, stdout, session_path)
                continue
            except EOFError:
                return 0
            if out:
                print(out, file=stdout)

    def _open_session(self, stdout):
        """每个会话自动记录成一个代码文件（sessions/ 目录，可回放）。"""
        import os
        import time
        session_dir = os.path.join(os.path.dirname(os.path.dirname(__file__)), "sessions")
        os.makedirs(session_dir, exist_ok=True)
        path = os.path.join(session_dir, time.strftime("%Y%m%d-%H%M%S") + ".repl")
        with open(path, "w", encoding="utf-8") as f:
            f.write(f"# py-nanobruijn 会话记录 {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"# 回放：python -m py_nanobruijn repl < {os.path.basename(path)}\n")
        print(f"会话已记录: {os.path.relpath(path, os.getcwd())}", file=stdout)
        return path

    @staticmethod
    def _record_session(path: str | None, line: str) -> None:
        if path:
            with open(path, "a", encoding="utf-8") as f:
                f.write(line.rstrip("\n") + "\n")

    def _run_proof(self, state: ProofState, stdin, stdout, session_path: str | None = None) -> None:
        """#prove 子循环：proof> 提示符；done/#quit/abort/EOF 退出回到主循环。"""
        print(f"证明: {pretty(self.core, state.goal_ty, self.color)}", file=stdout)
        print(state.context(), file=stdout)
        while True:
            try:
                prompt = self._c("proof> ", "green")
                line = input(prompt) if stdin is sys.stdin else stdin.readline()
            except EOFError:
                return
            if not line:
                if stdin is not sys.stdin:
                    return
                continue
            if line.strip() == "#quit":
                return
            self._record_session(session_path, line)
            try:
                out = run_tactic(state, line)
            except ProofDone as done:
                print(done.text, file=stdout)
                return
            except AbortProof:
                return
            except (ValueError, ParseError, CheckTimeoutError) as err:
                print(self._error(str(err)), file=stdout)
                continue
            except Exception as err:  # noqa: BLE001 - REPL 顶层兜底
                print(self._error(f"{type(err).__name__}: {err}"), file=stdout)
                continue
            if out:
                print(out, file=stdout)