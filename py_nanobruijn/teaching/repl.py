from __future__ import annotations

import os
import sys

from ..errors import CheckTimeoutError, ParseError
from ..ptr import ExprPtr
from .core import BootstrapCore
from .game import GameLoader, GameSession
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


class _GameSession(Exception):
    """process_line 的内部信号：进入 #game 游戏子循环（由 run() 捕获）。"""

    def __init__(self, session):
        super().__init__("game session")
        self.session = session


class Repl:
    def __init__(self, core: BootstrapCore, timeout_secs: float = 5.0,
                 color: bool | None = None):
        self.core = core
        self.timeout_secs = float(timeout_secs)
        self.color = color_enabled(color)
        self.pending_game = None

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
        if cmd == "worlds":
            return self._worlds()
        if cmd == "game":
            return self._game(rest)
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

    def _worlds(self) -> str:
        import glob
        lines = []
        for path in sorted(glob.glob(os.path.join(
                os.path.dirname(os.path.dirname(__file__)), "worlds", "*.game"))):
            game = GameLoader().load(path)
            prog = GameSession(game)
            prog.load_progress()
            stars = f"{len(prog.stars)}/5 关"
            lines.append(f"{game.world_id} — {game.title}（{stars}）")
        return "\n".join(lines) or "（暂无世界，worlds/ 目录为空）"

    def _game(self, text: str) -> str:
        text = text.strip()
        if not text:
            return "usage: #game <世界>（如 #game And；#worlds 查看全部）"
        err = self.start_game(text)
        if err:
            return self._error(err)
        raise _GameSession(self.pending_game)

    def start_game(self, world_id: str) -> str | None:
        """加载世界并构造会话（失败返回错误文本）。"""
        import glob
        path = os.path.join(os.path.dirname(os.path.dirname(__file__)),
                            "worlds", world_id.lower() + ".game")
        if not os.path.exists(path):
            known = sorted(os.path.basename(p)[:-5] for p in glob.glob(
                os.path.join(os.path.dirname(os.path.dirname(__file__)),
                             "worlds", "*.game")))
            return f"未知世界 {world_id!r}（可选：{', '.join(known)}）"
        game = GameLoader().load(path)
        session = GameSession(game)
        session.load_progress()
        self.pending_game = session
        return None

    STEP_TACTICS = ('intro', 'apply', 'exact', 'cases')

    # ---------- 主循环 ----------

    def run(self, stdin=None, stdout=None) -> int:
        stdin = stdin or sys.stdin
        stdout = stdout or sys.stdout
        print(BANNER, file=stdout)
        print(f"已加载 {len(self.core.constants())} 个常量，输入 #help 查看帮助", file=stdout)
        session_path = self._open_session(stdout)
        while True:
            try:
                if self.pending_game is not None:
                    game = self.pending_game
                    self.pending_game = None
                    self._run_game(game, stdin, stdout, session_path)
                    continue
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
            except _GameSession as session:
                self.pending_game = session.session
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

    def _run_game(self, game, stdin, stdout, session_path) -> None:
        print(f"{game.game.title}", file=stdout)
        print(f"{game.game.intro}", file=stdout)
        while True:
            no = game.next_unfinished()
            if no is None:
                print(self._c("🎉 世界通关！全部关卡完成。", "green"), file=stdout)
                return
            level = game.game.level(no)
            name = level.name or ""
            print(f"\n{self._c(f'第 {no} 关：{name}', 'green')}", file=stdout)
            try:
                goal_ty = parse_expr(self.core, level.goal)
                state = ProofState(self.core, goal_ty, self.timeout_secs, self.color)
            except (ValueError, ParseError) as err:
                print(self._error(f"关卡 goal 解析失败: {err}"), file=stdout)
                return
            game.current_level_no = no
            status = self._run_proof(state, stdin, stdout, session_path,
                                     level=level, game=game)
            if status == "abandoned":
                return

    def _game_tactic_check(self, level, line: str) -> str | None:
        head = line.strip().split(maxsplit=1)[0].rstrip(';')
        if head in level.bans:
            guide = level.hints[0] if level.hints else "想想 apply/exact 怎么构造"
            return f"本关禁用 {head}——{guide}"
        return None

    def _run_proof(self, state: ProofState, stdin, stdout,
                   session_path: str | None = None, *,
                   level=None, game=None) -> str:
        """#prove 子循环：proof> 提示符；done/#quit/abort/EOF 退出回到主循环。

        返回 "completed"（通关/完成）或 "abandoned"（放弃）。level/game 非空时
        处于游戏关卡内：hint/solution 命令、ban 检查、步数计数、星级存档。
        """
        if level is not None:
            print(state.context(), file=stdout)
        else:
            print(f"证明: {pretty(self.core, state.goal_ty, self.color)}", file=stdout)
            print(state.context(), file=stdout)
        steps = 0
        used_hint = False
        hint_idx = 0
        while True:
            try:
                prompt = self._c("proof> ", "green")
                line = input(prompt) if stdin is sys.stdin else stdin.readline()
            except EOFError:
                return "abandoned" if level is not None else "completed"
            if not line:
                if stdin is not sys.stdin:
                    return "abandoned" if level is not None else "completed"
                continue
            if line.strip() == "#quit":
                return "abandoned" if level is not None else "completed"
            self._record_session(session_path, line)
            if level is not None:
                cmd = line.strip()
                if cmd == "hint":
                    if hint_idx < len(level.hints):
                        hint = level.hints[hint_idx]
                        hint_idx += 1
                        used_hint = True
                        print(f"提示 {hint_idx}/{len(level.hints)}: {hint}", file=stdout)
                    else:
                        print("没有更多提示了——再想想，或者 solution 看标准解", file=stdout)
                    continue
                if cmd == "solution":
                    print("标准解：", file=stdout)
                    print("\n".join(level.solution), file=stdout)
                    print(self._c("（本关未通关。quit 或继续尝试）", "gray"), file=stdout)
                    return "abandoned"
                blocked = self._game_tactic_check(level, line)
                if blocked:
                    print(self._error(blocked), file=stdout)
                    continue
                if line.strip().split(maxsplit=1)[0] in self.STEP_TACTICS:
                    steps += 1
            try:
                out = run_tactic(state, line)
            except ProofDone as done:
                print(done.text, file=stdout)
                if level is not None and game is not None:
                    stars = game.complete(steps, used_hint)
                    print(self._c(f"过关！获得 {'★' * stars}{'☆' * (3 - stars)}", 'green'), file=stdout)
                    if level.solution:
                        print("标准解（你的路径可能不同，两种都正确）：", file=stdout)
                        print("\n".join(level.solution), file=stdout)
                return "completed"
            except AbortProof:
                return "abandoned"
            except (ValueError, ParseError, CheckTimeoutError) as err:
                print(self._error(str(err)), file=stdout)
                continue
            except Exception as err:  # noqa: BLE001 - REPL 顶层兜底
                print(self._error(f"{type(err).__name__}: {err}"), file=stdout)
                continue
            if out:
                print(out, file=stdout)