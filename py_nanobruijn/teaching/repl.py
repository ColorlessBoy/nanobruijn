from __future__ import annotations

import os
import sys

from ..errors import CheckTimeoutError, ParseError
from ..ptr import ExprPtr
from .core import BootstrapCore
from .game import SAVES_DIR, GameLoader, GameSession, load_world_order, resolve_profile
from .parser import parse_expr
from .pretty import pretty
from .proof import ProofState
from .reduce import reduce_steps, show_reduction
from .style import color_enabled, colorize
from .tactics import AbortProof, ProofDone, run_tactic

BANNER = (
    "py-nanobruijn teaching REPL\n"
    "输入表达式查看类型（等价 #check），或使用命令："
    "#check/#reduce/#print/#def/#prove/#env/#pp/#help/#exit\n"
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


_CIRCLED = "①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯⑰⑱⑲⑳"


class Repl:
    def __init__(self, core: BootstrapCore, timeout_secs: float = 5.0,
                 color: bool | None = None, saves_dir: str | None = None,
                 fresh: bool = False, save_name: str | None = None,
                 save_new: bool = False, saves_root: str | None = None):
        self.core = core
        self.timeout_secs = float(timeout_secs)
        self.color = color_enabled(color)
        self.fresh = fresh  # --fresh：空 env 起步，世界进入时现场定义
        self._loaded_fragments: set[str] = set()
        from .reporting import LearningLog
        self.learning = LearningLog(fresh)
        self.pending_game = None
        self._intro_shown: set[str] = set()
        self._lesson_shown: set[str] = set()
        self._last_game: GameSession | None = None
        # 存档 profile：显式 saves_dir 直接作为档位目录（嵌入用）；
        # 否则在 saves_root（默认 SAVES_DIR）下解析
        # （命名档 / 新档 / 续玩 mtime 最新档）
        if saves_dir is not None:
            self.saves_dir = saves_dir
            self.saves_root = os.path.dirname(os.path.abspath(saves_dir))
        else:
            self.saves_root = saves_root or SAVES_DIR
            self.saves_dir = resolve_profile(self.saves_root, save_name,
                                             save_new)

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
        if text == "hint":
            return ("提示只在关卡内可用（#game <世界> 进入后，proof> 提示符下输入 hint）")
        if text == "solution":
            return ("标准解只在关卡内可用（#game <世界> 进入后，proof> 提示符下输入 solution）")
        if text in ("exit", "#exit"):
            raise EOFError()
        if text.startswith("#"):
            return self._command(text)
        return self._check(text)

    def _command(self, text: str) -> str:
        parts = text[1:].split(maxsplit=1)
        cmd = parts[0]
        rest = parts[1] if len(parts) > 1 else ""
        if cmd == "help":
            return BANNER
        if cmd == "exit":
            raise EOFError()
        if cmd == "env":
            return "\n".join(self.core.constants())
        if cmd == "print":
            return self._print_const(rest)
        if cmd == "def":
            return self._def_declare(rest)
        if cmd == "reduce":
            return self._run_reduce(rest)
        if cmd == "check":
            return self._check(rest)
        if cmd == "prove":
            return self._prove(rest)
        if cmd == "pp":
            return self._pp_mode(rest)
        if cmd == "game":
            return self._game(rest)
        if cmd == "lesson":
            return self._lesson_cmd()
        if cmd == "example":
            return self._example_cmd()
        if cmd == "saves":
            return self._saves()
        if cmd == "vocab":
            return self._vocab()
        return f"unknown command #{cmd} (try #help)"

    def _pp_mode(self, text: str) -> str:
        """#pp：显示模式切换。on = Lean 可读（隐式隐藏/记号/⟨⟩），off = 内核精确。"""
        t = text.strip().lower()
        if t == "on":
            self.core.pp_readable = True
            return "pp 模式：readable（Lean 风格：隐式参数隐藏、= ∧ ∨ ↔ ¬、⟨…⟩；#pp off 切回）"
        if t == "off":
            self.core.pp_readable = False
            return "pp 模式：exact（内核精确：@Const/宇宙标注/完整参数）"
        cur = "readable" if getattr(self.core, "pp_readable", False) else "exact"
        return f"pp 模式：{cur}（用法：#pp on | #pp off）"

    def _check(self, text: str) -> str:
        try:
            e = parse_expr(self.core, text)
            if self._has_nat_lit(e):
                return self._error("Nat 字面量的类型推断在 v1 教学核心中暂不支持（需要 Nat inductive 类型）")
            tc = self.core.make_type_checker(self.timeout_secs)
            ty = tc.infer(e, 'check')
            return f"{pretty(self.core, e, self.color)} : {pretty(self.core, ty, self.color)}"
        except ParseError as err:
            msg = str(err)
            if self.fresh and ('unknown constant' in msg
                               or 'unknown identifier' in msg):
                name = msg.split("'")[1] if "'" in msg else '?'
                return self._error(
                    f"{name} 还没被定义！"
                    f"（#game 看世界列表，进对应世界见证它的定义）")
            return self._error(msg)
        except (ValueError, CheckTimeoutError) as err:
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

    def _def_declare(self, text: str) -> str:
        """#def <fol 声明>：学生亲手定义（axiom/def/theorem，多行 := 续行）。"""
        from .fol import load_fol_lines
        text = text.strip()
        if not text:
            return ("usage: #def axiom Nand : Prop -> Prop -> Prop\n"
                    "       #def定理名 : 类型\n       := 值（多行可继续输）")
        # 单行含 := 值：拆成 声明行 + ":= 值" 两行（与 fol 文件续行一致）
        if ':=' in text and not text.lstrip().startswith(':='):
            decl, val = text.split(':=', 1)
            lines = [decl.strip(), ':= ' + val.strip()]
        else:
            lines = [text]
        before = set(self.core.env.declars)
        try:
            load_fol_lines(self.core, lines)
        except (ValueError, ParseError) as err:
            msg = str(err).removeprefix('fol: ')
            return self._error(f"#def 声明无法解析：{msg}")
        except Exception as err:  # noqa: BLE001
            return self._error(f"{type(err).__name__}: {err}")
        new = sorted(self.core.name_to_string(n) for n in self.core.env.declars
                     if n not in before)
        if not new:
            return self._error("#def: 没有产生新声明（重复定义？）")
        kind = ('公理' if lines[0].startswith('axiom')
                else '定理' if lines[0].startswith('theorem') else '定义')
        self.learning.add_definition(new[0], kind)
        out = self._c(f"✚ {kind}已加入环境：{'、'.join(new)}", 'green')
        # 教学彩蛋：类型恰为 False 的公理会引爆一致性
        if lines[0].startswith('axiom') and ': False' in lines[0]:
            out += ("\n" + self._c(
                "⚠️ 注意：这个公理让 False 有了证明——从现在起你可以"
                "『证明』一切（爆炸原理）。试试 #prove forall (a : Prop), a",
                'yellow'))
        out += "\n现在可以 #check 它、在 #prove 里使用它。"
        return out

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

    def _worlds_dir(self) -> str:
        return os.path.join(os.path.dirname(os.path.dirname(__file__)),
                            "worlds")

    def _next_world_hint(self, world_id: str) -> str | None:
        """课程依赖拓扑序中的下一站（未知世界/末尾返回 None）。"""
        try:
            order = load_world_order(self._worlds_dir())
            i = order.index(world_id)
        except ValueError:
            return None
        return order[i + 1] if i + 1 < len(order) else None

    def _worlds(self) -> str:
        try:
            order = load_world_order(self._worlds_dir())
            games = {g.world_id: g for g in GameLoader.load_all(self._worlds_dir())}
        except ValueError as err:
            return self._error(str(err))
        lines = []
        for i, wid in enumerate(order, 1):
            game = games[wid]
            prog = GameSession(game, saves_dir=self.saves_dir)
            prog.load_progress()
            stars = "".join(str(prog.stars.get(lv.number, "-"))
                            for lv in game.levels)
            num = _CIRCLED[i - 1] if i <= len(_CIRCLED) else f"{i}."
            lines.append(f"{num} {game.world_id} — {game.title}"
                         f"（{len(prog.stars)}/{len(game.levels)} 关，"
                         f"星级 {stars}）")
        return "\n".join(lines) or "（暂无世界，worlds/ 目录为空）"

    def _vocab(self) -> str:
        """#vocab：Lean 4 单词表——主线引导，按进度点亮。"""
        from .vocab import VOCAB, annotate, render_plain
        d = self._worlds_dir()
        order = load_world_order(d)
        current = None
        if self._last_game is not None:
            current = self._last_game.game.world_id
        else:
            for wid in order:
                g = GameLoader().load(os.path.join(d, wid.lower() + ".game"))
                s = GameSession(g, saves_dir=self.saves_dir)
                s.load_progress()
                if s.next_unfinished() is not None:
                    current = wid
                    break
        entries = annotate(VOCAB, current, order)
        head = (f"Lean 4 词表索引（当前世界：{current or '未开始'}；✓已学 ●本世界 ○待学）\n"
                "（复习用——每个词的正式教学在对应世界的课堂里）\n")
        return head + render_plain(entries)

    def _saves(self) -> str:
        """#saves：列出全部存档档位（关数/星数，当前档位标记）。"""
        root = self.saves_root
        if not root or not os.path.isdir(root):
            return "（无存档目录）"
        profiles = sorted(
            (e for e in os.listdir(root)
             if os.path.isdir(os.path.join(root, e))),
            key=lambda e: os.path.getmtime(os.path.join(root, e)),
            reverse=True)
        if not profiles:
            return "（暂无存档档位）"
        try:
            games = {g.world_id: g for g in GameLoader.load_all(self._worlds_dir())}
        except ValueError:
            games = {}
        cur = os.path.basename(os.path.normpath(self.saves_dir))
        lines = []
        for p in profiles:
            done = stars = total = 0
            for g in games.values():
                s = GameSession(g, saves_dir=os.path.join(root, p))
                s.load_progress()
                total += len(g.levels)
                done += len(s.stars)
                stars += sum(s.stars.values())
            mark = "（当前）" if p == cur else ""
            lines.append(f"{p} — {done}/{total} 关，{stars}★{mark}")
        return "\n".join(lines)

    def _game(self, text: str) -> str:
        text = text.strip()
        if not text:
            listing = self._worlds()
            return (f"{listing}\n\n进入：#game <世界>；指定关卡：#game <世界> <关卡号>；"
                    f"重玩整个世界：#game <世界> replay")
        parts = text.split()
        replay = len(parts) > 1 and parts[1] == "replay"
        if replay and len(parts) > 2:
            return self._error("replay 不接受关卡号——整个世界从第 1 关重打")
        level_no = None
        if len(parts) > 1 and not replay:
            try:
                level_no = int(parts[1])
            except ValueError:
                return self._error(f"关卡号必须是数字：{parts[1]!r}")
        err = self.start_game(parts[0], level_no, replay=replay)
        if err:
            return self._error(err)
        raise _GameSession(self.pending_game)

    def start_game(self, world_id: str, level_no: int | None = None,
                   replay: bool = False) -> str | None:
        """加载世界并构造会话（失败返回错误文本；level_no 指定进入关卡）。

        replay=True：重玩模式——进度视图清零从第 1 关开始，历史最佳保留。
        """
        import glob
        path = os.path.join(os.path.dirname(os.path.dirname(__file__)),
                            "worlds", world_id.lower() + ".game")
        if not os.path.exists(path):
            known = sorted(os.path.basename(p)[:-5] for p in glob.glob(
                os.path.join(os.path.dirname(os.path.dirname(__file__)),
                             "worlds", "*.game")))
            return f"未知世界 {world_id!r}（可选：{', '.join(known)}）"
        game = GameLoader().load(path)
        session = GameSession(game, saves_dir=self.saves_dir, replay=replay)
        session.load_progress()
        if level_no is not None:
            if not 1 <= level_no <= len(game.levels):
                return f"关卡号 {level_no} 超出范围（1-{len(game.levels)}）"
            session.force_level(level_no)
        self.pending_game = session
        return None

    STEP_TACTICS = ('intro', 'apply', 'exact', 'cases', 'rewrite')

    # ---------- 主循环 ----------

    def _auto_resume(self, stdout) -> None:
        """交互启动时按当前存档档位续玩：拓扑序第一个进行中的世界。

        只由 run() 在交互模式（stdin is sys.stdin）下调用——
        --script/--json 通道绝不自动进游戏，防止脚本行落入 proof> 提示符。
        只考虑玩过的世界（有星标记录）；都没通关时推荐下一站。
        """
        d = self._worlds_dir()
        if not os.path.isdir(d):
            return
        try:
            games = {g.world_id: g for g in GameLoader.load_all(d)}
        except ValueError:
            return
        next_station = None
        played_any = False
        for wid in load_world_order(d):
            session = GameSession(games[wid], saves_dir=self.saves_dir)
            session.load_progress()
            if not session.stars:
                if next_station is None:
                    next_station = wid
                continue
            played_any = True
            nxt = session.next_unfinished()
            if nxt is not None:
                self.pending_game = session
                print(self._c(
                    f"欢迎回来——续玩：{wid} 世界（第 {nxt} 关起，"
                    f"#game 看世界列表）", "cyan"), file=stdout)
                return
        if played_any:
            if next_station:
                print(self._c(
                    f"当前存档已通关——下一站：{next_station} 世界"
                    f"（#game {next_station}）", "cyan"), file=stdout)
            else:
                print(self._c("🎉 全部世界通关——自由模式（#saves 管理存档）",
                              "green"), file=stdout)

    def run(self, stdin=None, stdout=None) -> int:
        stdin = stdin or sys.stdin
        stdout = stdout or sys.stdout
        print(BANNER, file=stdout, flush=True)
        if self.fresh:
            print(self._c(
                "本会话从空环境开始——逻辑词会在进入世界时现场定义"
                "（定义仪式）。用 #game 看世界列表。", 'cyan'), file=stdout)
        print(f"已加载 {len(self.core.constants())} 个常量，输入 #help 查看帮助", file=stdout)
        session_path = self._open_session(stdout)
        if self.pending_game is None and stdin is sys.stdin:
            self._auto_resume(stdout)
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
                self._save_learning_report(stdout)
                return 0
            if not line:
                if stdin is not sys.stdin:
                    self._save_learning_report(stdout)
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

    def _save_learning_report(self, stdout) -> None:
        """会话结束：有做题记录则生成学习报告（reports/）。"""
        if not self.learning.entries and self.learning.current is None:
            return
        try:
            path = self.learning.save_report(self._data_dir("reports"))
            print(self._c(f"学习报告已生成：{path}", 'cyan'), file=stdout)
        except OSError:
            pass

    def _ask_report(self, stdin, stdout) -> None:
        """连错后询问玩家是否上报问题（交互模式才调用）。"""
        print(self._c("连续几次没通过——要上报这个问题吗？（y/n，可附一句话）",
                      'cyan'), file=stdout)
        try:
            answer = stdin.readline().strip()
        except (EOFError, OSError):
            return
        note = ""
        if answer.lower().startswith("y"):
            rest = answer[1:].strip()
            if not rest:
                print("一句话描述问题（可直接回车跳过）：", file=stdout)
                try:
                    note = stdin.readline().strip()
                except (EOFError, OSError):
                    note = ""
            path = self.learning.save_feedback(
                self._data_dir("feedback"), note)
            print(self._c(f"反馈已保存：{path}（可发给老师或附在 issue 里）",
                          'green'), file=stdout)

    def _data_dir(self, kind: str) -> str:
        import os
        return os.path.join(os.path.dirname(os.path.dirname(__file__)), kind)

    @staticmethod
    def _record_session(path: str | None, line: str) -> None:
        if path:
            with open(path, "a", encoding="utf-8") as f:
                f.write(line.rstrip("\n") + "\n")

    def _run_game(self, game, stdin, stdout, session_path) -> None:
        self._definition_ceremony(game, stdout)
        if game.game.world_id not in self._intro_shown:
            print(f"{game.game.title}", file=stdout)
            print(f"{game.game.intro}", file=stdout)
            self._intro_shown.add(game.game.world_id)
        self._last_game = game
        if (game.game.world_id not in self._lesson_shown and not game.stars):
            self._show_lessons(game.game, stdin, stdout)
            self._run_example(game.game, stdin, stdout)
        self._lesson_shown.add(game.game.world_id)
        while True:
            no = game.next_unfinished()
            if no is None:
                print(self._c("🎉 世界通关！全部关卡完成。", "green"), file=stdout)
                nxt = self._next_world_hint(game.game.world_id)
                if nxt:
                    print(self._c(f"下一站：{nxt} 世界——#game {nxt}", "cyan"),
                          file=stdout)
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
            self.learning.start_level(game.game.world_id, no,
                                      name, level.goal)
            status = self._run_proof(state, stdin, stdout, session_path,
                                     level=level, game=game)
            if status == "retry":
                game.force_level(no)  # solution 后重新开始本关（可复制标准解）
            elif status == "completed" and getattr(game, "_came_from_force", False):
                # 直达重玩（#game <世界> <关卡>）：通关后顺延下一关，不回绕
                game.advance_after(no)
            elif status == "abandoned":
                return

    def _show_lessons(self, game, stdin, stdout) -> None:
        """世界课堂：lesson 段落逐段展示（交互模式回车翻页）。"""
        if not game.lessons:
            return
        print(self._c("📖 课堂", "cyan"), file=stdout)
        for i, para in enumerate(game.lessons):
            print(f"  {para}", file=stdout)
            if stdin is sys.stdin and i < len(game.lessons) - 1:
                try:
                    input(self._c("  （回车继续）", "gray"))
                except EOFError:
                    return

    def _run_example(self, game, stdin, stdout) -> None:
        """演示关：逐步执行 example: 脚本（不计星、不记学习日志）。

        交互模式回车步进；非交互（--script/--json）一次性输出。
        演示脚本损坏只报错跳过，不阻断游戏流程。
        """
        if not game.example_goal or not game.example:
            return
        print(self._c(f"🎬 演示关：{game.example_goal}", "cyan"), file=stdout)
        try:
            goal_ty = parse_expr(self.core, game.example_goal)
        except (ValueError, ParseError) as err:
            print(self._error(f"演示关 goal 解析失败: {err}"), file=stdout)
            return
        state = ProofState(self.core, goal_ty, self.timeout_secs, self.color)
        for line in game.example:
            print(f"{self._c('proof>', 'green')} {line}", file=stdout)
            try:
                out = run_tactic(state, line)
            except ProofDone as done:
                print(done.text, file=stdout)
                break
            except Exception as err:  # noqa: BLE001 - 演示脚本兜底
                print(self._error(f"{type(err).__name__}: {err}"), file=stdout)
                break
            if out:
                print(out, file=stdout)
            if stdin is sys.stdin:
                try:
                    input(self._c("  （回车继续）", "gray"))
                except EOFError:
                    break
        print(self._c("（演示完毕——下面开始你的第一关）", "gray"), file=stdout)

    def _lesson_cmd(self) -> str:
        if self._last_game is None:
            return "先 #game <世界> 进入一个世界（#game 看列表）"
        g = self._last_game.game
        if not g.lessons:
            return f"{g.world_id} 世界没有课堂内容"
        return "\n".join(g.lessons)

    def _example_cmd(self) -> str:
        if self._last_game is None:
            return "先 #game <世界> 进入一个世界（#game 看列表）"
        import io
        buf = io.StringIO()
        self._run_example(self._last_game.game, io.StringIO(), buf)
        text = buf.getvalue().strip()
        return text or f"{self._last_game.game.world_id} 世界没有演示关"

    def _definition_ceremony(self, game, stdout) -> None:
        """定义仪式：按世界 using: 现场加载 fol 片段（fresh 模式真实加载，
        全量模式显示复习表——"它们已在你的环境中"）。"""
        from .fol import FRAGMENT_ROLES, fragment_source, resolve_deps
        using = game.game.using or []
        if not using:
            return
        todo = ([f for f in resolve_deps(using)
                 if f not in self._loaded_fragments] if self.fresh else [])
        if not todo and self.fresh:
            return
        print(self._c(f"📜 定义仪式：{game.game.title}", 'cyan'), file=stdout)
        for frag in resolve_deps(using):
            if not self.fresh:
                role = FRAGMENT_ROLES.get(frag, '')
                print(self._c(f"  {frag} — {role}（已在环境中）", 'gray'),
                      file=stdout)
                continue
            src = fragment_source(frag)
            print(self._c(f"--- {frag} ---", 'gray'), file=stdout)
            for line in src.splitlines():
                if not line.strip():
                    continue
                if line.startswith('#'):  # 教学注解：灰字保留
                    print(self._c(f"  {line}", 'gray'), file=stdout)
                    continue
                if line.startswith('  :='):  # 定理证明体：跳过（签名即教学）
                    continue
                if line.startswith(('axiom ', 'def ', 'theorem ')):
                    head = line.split(':')[0]
                    if len(line) > 110:  # 长签名（消去规则等）：折叠
                        name = head.split(' ')[1].split('{')[0]
                        print(f"  {head}: …（完整类型用 #print {name} 查看）")
                        continue
                print(f"  {line}", file=stdout)
            new_names = self.core.load_fragment(frag)
            self._loaded_fragments.add(frag)
            print(self._c(
                f"  ✚ 已定义 {len(new_names)} 个常量："
                f"{'、'.join(new_names)}", 'green'), file=stdout)

    def _game_tactic_check(self, level, line: str) -> str | None:
        for part in line.split(';'):
            head = part.strip().split(maxsplit=1)[0]
            if head in level.bans:
                return (f"本关禁用 {head}——这关故意不给你这条捷径，"
                        f"换一条路想想（线索看 hint，hint 会扣星）")
        return None

    def _run_proof(self, state: ProofState, stdin, stdout,
                   session_path: str | None = None, *,
                   level=None, game=None) -> str:
        """#prove 子循环：proof> 提示符；done/exit/EOF 退出回到主循环。

        返回 "completed"（通关/完成）或 "abandoned"（放弃）。level/game 非空时
        处于游戏关卡内：hint/solution 命令、ban 检查、步数计数、星级存档。
        """
        if level is not None:
            print(state.context(), file=stdout)
        else:
            print(f"证明: {pretty(self.core, state.goal_ty, self.color)}", file=stdout)
            print(state.context(), file=stdout)
        steps = 0
        hint_idx = 0
        error_streak = 0
        asked_report = False
        while True:
            try:
                prompt = self._c("proof> ", "green")
                line = input(prompt) if stdin is sys.stdin else stdin.readline()
            except EOFError:
                if level is not None:
                    self.learning.abandon()
                return "abandoned" if level is not None else "completed"
            if not line:
                if stdin is not sys.stdin:
                    if level is not None:
                        self.learning.abandon()
                    return "abandoned" if level is not None else "completed"
                continue
            self._record_session(session_path, line)
            if level is not None:
                cmd = line.strip()
                if cmd == "hint":
                    if hint_idx < len(level.hints):
                        hint = level.hints[hint_idx]
                        hint_idx += 1
                        self.learning.hint_used()
                        print(f"提示 {hint_idx}/{len(level.hints)}: {hint}", file=stdout)
                    else:
                        print("没有更多提示了——再想想，或者 solution 看标准解", file=stdout)
                    continue
                if cmd == "solution":
                    self.learning.abandon()
                    print("标准解：", file=stdout)
                    print("\n".join(level.solution), file=stdout)
                    print(self._c("（本关未通关——输入任意命令重新开始本关，或 exit 回主 REPL）", "gray"), file=stdout)
                    return "retry"
                blocked = self._game_tactic_check(level, line)
                if blocked:
                    print(self._error(blocked), file=stdout)
                    continue
                is_step = line.strip().split(maxsplit=1)[0] in self.STEP_TACTICS
            else:
                is_step = False
            self.learning.record(line)
            try:
                out = run_tactic(state, line)
                error_streak = 0
            except ProofDone as done:
                if level is not None and is_step:
                    steps += 1
                print(done.text, file=stdout)
                if level is not None and game is not None:
                    stars = game.complete(steps, hint_idx)
                    self.learning.finish_level(stars)
                    print(self._c(f"过关！获得 {'★' * stars}{'☆' * (3 - stars)}", 'green'), file=stdout)
                    if level.solution:
                        print("标准解（你的路径可能不同，两种都正确）：", file=stdout)
                        print("\n".join(level.solution), file=stdout)
                    for variant in level.variants:
                        print(self._c(f"💡 变体挑战：{variant}", 'cyan'), file=stdout)
                return "completed"
            except AbortProof:
                if level is not None:
                    self.learning.abandon()
                return "abandoned"
            except (ValueError, ParseError, CheckTimeoutError) as err:
                msg = str(err)
                self.learning.record_error(msg)
                if level is not None and not is_step:
                    pass
                error_streak += 1
                print(self._error(msg), file=stdout)
                # 连错 3 次：交互模式下询问是否上报
                if (error_streak >= 3 and not asked_report
                        and stdin is sys.stdin and level is not None):
                    asked_report = True
                    self._ask_report(stdin, stdout)
                continue
            except Exception as err:  # noqa: BLE001 - REPL 顶层兜底
                print(self._error(f"{type(err).__name__}: {err}"), file=stdout)
                continue
            if is_step:
                steps += 1
            if out:
                print(out, file=stdout)