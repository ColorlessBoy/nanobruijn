"""Textual TUI：agent 式教学流（参照 opencode / rustlings / Ink 系 agent CLI）。

形态：滚动对话流（仪式/课堂/反馈以消息卡追加）+ 常驻习题卡（in-place 更新
上下文/目标/当前项）+ 世界与常量侧栏 + 单输入行。

架构：WebApp（无头引擎，见 web_server.py）+ 本文件 = 该引擎的终端客户端。
启动：python -m py_nanobruijn tui
"""
from __future__ import annotations

import json
from typing import Any, ClassVar

from textual import on
from textual.app import App, ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll
from textual.widgets import Footer, Header, Input, Markdown, OptionList, Static
from textual.widgets.option_list import Option

from .game import load_world_order
from .llm import TOOLS
from .web_server import WebApp

CIRCLED = "①②③④⑤⑥⑦⑧⑨⑩⑪"


def _stars(n: int) -> str:
    return f"[#ffd166]{'★' * n}[/][#3a4356]{'☆' * (3 - n)}[/]"


def _term_rich(term: str) -> str:
    return term.replace("_", "[#ffb454]_[/]")


class WorldList(OptionList):
    """侧栏：①-⑪ 世界（课程拓扑序 + 进度 + 星标）。"""


class ConstList(OptionList):
    """侧栏：环境常量（可搜索；回车 #print）。"""


class ExerciseCard(Static):
    """常驻习题卡：进入关卡后随每次 tactic 就地更新。"""

    DEFAULT_CSS = """
    ExerciseCard { border: round #4fa3ff; background: #121826;
                   padding: 1 2; margin: 1 0; width: 100%; }
    """

    def update_exercise(self, level: dict[str, Any], ctx: dict[str, Any]) -> None:
        self.level = level      # 测试断言钩子（最后一次渲染的载荷）
        self.ctx = ctx
        chips = "\n".join(f"  [b]{n}[/] : [dim]{ty}[/]" for n, ty in ctx["context"]) \
            or "  [dim]（空——还没有引入任何假设）[/]"
        note = f"\n[dim]{ctx['note']}[/]" if ctx.get("note") else ""
        self.update(
            f"[b]第 {level['number']} 关：{level['name']}[/]"
            f"  [dim]{level['goal']}[/]\n\n"
            f"[#4fa3ff]上下文[/]\n{chips}\n\n"
            f"[#4fa3ff]目标——需要写出一个类型如下的项[/]\n"
            f"  [#ffb454]?[/] : {ctx['goal']}\n\n"
            f"[#4fa3ff]当前项 λ[/]\n[dim]{_term_rich(ctx['term'])}[/]"
            + note)


class NanobruijnTui(App[None]):
    TITLE = "nanobruijn"
    SUB_TITLE = "证明游戏"

    CSS = """
    #body { height: 1fr; }
    #sidebar { width: 36; border-right: solid #2a3242; background: #171d29; }
    #sidebar .label { color: #8b95a8; padding: 1 2; }
    #sidebar Input { border: none; height: 3; background: #1d2534; margin: 0 1 1 1; }
    WorldList, ConstList { background: #171d29; height: 1fr; border: none; }
    #chat { padding: 1 2; }
    .msg { margin: 0; color: #d7dde8; }
    .msg-dim { margin: 0; color: #8b95a8; }
    .msg-ok { margin: 0; color: #3ecf8e; }
    .msg-err { margin: 0; color: #ff6b6b; }
    .msg-warn { margin: 0; color: #ffb454; }
    .msg-hl { margin: 0; color: #4fa3ff; }
    #command-in { border: none; border-top: solid #2a3242; background: #171d29; }
    """

    BINDINGS: ClassVar[list] = [
        ("escape", "back", "返回列表"),
        ("f2", "hint", "提示"),
        ("f3", "solution", "标准解"),
    ]

    def __init__(self, saves_dir: str | None = None):
        super().__init__()
        self.engine = WebApp(saves_dir=saves_dir)
        self.entered: dict[str, Any] | None = None
        self.demo_steps: list[dict[str, Any]] = []
        self.demo_idx = 0
        self._consts: list[str] = []
        self._card: ExerciseCard | None = None

    # ---------- 组装 ----------

    def compose(self) -> ComposeResult:
        yield Header(show_clock=True)
        with Horizontal(id="body"):
            with Vertical(id="sidebar"):
                yield Static("世界（按课程顺序）", classes="label")
                yield WorldList(id="worlds")
                yield Static("常量（输入过滤，回车查看）", classes="label")
                yield Input(placeholder="查找常量…", id="const-filter")
                yield ConstList(id="consts")
            with Vertical(id="main"):
                yield VerticalScroll(id="chat")
        yield Input(placeholder="tactic / ask 问题 / #check / #game / hint / solution / exit / d",
                    id="command-in")
        yield Footer()

    def on_mount(self) -> None:
        self.refresh_sidebar()
        self.say("[b]nanobruijn 证明游戏[/]\n在内核眼里，证明就是一台机器。"
                 "选一个世界开始（侧栏点击，或 [#4fa3ff]#game And[/]）——"
                 "世界顺序即概念依赖链。")
        if self.engine.tutor.enabled:
            self.say(f"🤖 助教已连接（{self.engine.tutor.model}）——"
                     "内核报错时自动讲解；也可 [#4fa3ff]ask 你的问题[/]",
                     cls="msg-dim")
        else:
            self.say("[dim]🤖 助教未启用：设置 NANOBRUIJN_LLM_KEY"
                     "（OpenAI 兼容 API）后，内核报错会自动得到讲解，"
                     "且可用 ask <问题> 实时提问[/]", cls="msg-dim")
        data = self.engine.rpc("worlds")
        in_progress = next((w for w in data["worlds"]
                            if 0 < w["done"] < w["total"]), None)
        if in_progress:
            self.say(f"[#3ecf8e]欢迎回来——续玩：{in_progress['id']} 世界"
                     f"（第 {in_progress['done'] + 1} 关起，或 #game {in_progress['id']}）[/]")
        self.say("[dim]命令：#game（无参列表）/ #check / #reduce / #print / "
                 "hint / solution / exit / d（演示下一步）[/]")
        self.query_one("#command-in", Input).focus()

    # ---------- 对话流 ----------

    def _chat(self) -> VerticalScroll:
        return self.query_one("#chat", VerticalScroll)

    def say(self, text: str, cls: str = "msg") -> Static:
        card = Static(text, classes=cls)
        self._chat().mount(card)
        self._chat().scroll_end(animate=False)
        return card

    def say_md(self, text: str) -> Markdown:
        card = Markdown(text)
        self._chat().mount(card)
        self._chat().scroll_end(animate=False)
        return card

    # ---------- 侧栏 ----------

    def refresh_sidebar(self) -> None:
        data = self.engine.rpc("worlds")
        wl = self.query_one("#worlds", WorldList)
        wl.clear_options()
        for w in data["worlds"]:
            num = CIRCLED[w["index"] - 1] if w["index"] <= 11 else str(w["index"])
            star_str = " ".join(_stars(s) for s in w["stars"])
            wl.add_option(Option(
                f"[b]{num} {w['id']}[/] [dim]{w['title']}[/]\n"
                f"    {w['done']}/{w['total']} 关  {star_str}",
                id=w["id"]))
        self._consts = self.engine.rpc("constants")["constants"]
        self._render_consts("")

    def _render_consts(self, query: str) -> None:
        cl = self.query_one("#consts", ConstList)
        cl.clear_options()
        for c in self._consts:
            if query and query.lower() not in c.lower():
                continue
            cl.add_option(Option(c, id=c))

    @on(Input.Changed, "#const-filter")
    def on_const_filter(self, event: Input.Changed) -> None:
        self._render_consts(event.value)

    @on(OptionList.OptionSelected, "#worlds")
    def on_world_selected(self, event: OptionList.OptionSelected) -> None:
        if event.option_id:
            self.run_line(f"#game {event.option_id}")

    @on(OptionList.OptionSelected, "#consts")
    def on_const_selected(self, event: OptionList.OptionSelected) -> None:
        if event.option_id:
            self.run_line(f"#print {event.option_id}")

    # ---------- 世界进入 ----------

    def enter_world(self, world: str, replay: bool) -> None:
        out = self.engine.rpc("enter_world", world=world, replay=replay)
        if out["kind"] == "error":
            self.say(out["message"], cls="msg-err")
            return
        self.entered = out
        self.demo_steps = out["example"]["steps"]
        self.demo_idx = 0
        self.say(f"[b]{out['title']}[/]\n[dim]{out['intro']}[/]", cls="msg-hl")
        if out["definitions"]:
            self.say(out["definitions"], cls="msg-dim")
        self.say_md("\n\n".join(f"**📖 课堂**\n\n{p}" for p in out["lessons"]))
        self.say("[#4fa3ff]🎬 演示关[/]——看一遍完整的证明。"
                 "逐步输入 [b]d[/]；每步目标状态会打印在下面。", cls="msg")
        self.query_one("#command-in", Input).focus()

    def demo_next(self) -> None:
        if not self.entered or self.demo_idx >= len(self.demo_steps):
            return
        step = self.demo_steps[self.demo_idx]
        self.demo_idx += 1
        self.say(f"[#3ecf8e]proof>[/] {step['line']}", cls="msg-dim")
        if step.get("context"):
            self.say(f"  目标: [#ffb454]?[/] : {step['context']['goal']}", cls="msg-dim")
        if step.get("done"):
            self.say(step["done"], cls="msg-dim")
        if self.demo_idx >= len(self.demo_steps):
            self.say("[dim]（演示完毕——轮到你了）[/]", cls="msg-dim")
            self.spawn_exercise(self.entered["level"])

    def spawn_exercise(self, level: dict[str, Any]) -> None:
        """在流尾挂常驻习题卡（旧卡就地废弃）。"""
        self._card = ExerciseCard()
        self._chat().mount(self._card)
        assert self.entered is not None
        self._card.update_exercise(level, level["context"])
        self._chat().scroll_end(animate=False)
        self.query_one("#command-in", Input).focus()

    # ---------- 输入路由 ----------

    def run_line(self, line: str) -> None:
        line = line.strip()
        if not line:
            return
        if line in ("exit", "#exit", "#quit"):
            if self.engine.state == "level":
                out = self.engine.rpc("exit_level")
                self.say(out.get("note", "已离开关卡"), cls="msg-dim")
                self.entered = None
                self.refresh_sidebar()
            else:
                self.exit()
            return
        if line == "hint":
            out = self.engine.rpc("hint")
            if out["kind"] == "error":
                self.say(out["message"], cls="msg-err")
            else:
                self.say(f"💡 提示 {out['index']}/{out['total']}：{out['hint']}",
                         cls="msg-warn")
            return
        if line == "solution":
            out = self.engine.rpc("solution")
            if out["kind"] == "error":
                self.say(out["message"], cls="msg-err")
            else:
                self.say("标准解：\n" + "\n".join(out["solution"]), cls="msg-warn")
            return
        if line == "d":
            self.demo_next()
            return
        if line.startswith("ask "):
            self.start_tutor(line[4:].strip())
            return
        if line.startswith("#"):
            self.run_console_command(line)
            return
        if self.engine.state == "level":
            self.do_tactic(line)
        else:
            self.run_console_command(f"#check {line}")

    def do_tactic(self, line: str) -> None:
        out = self.engine.rpc("tactic", line=line)
        if out["kind"] == "error":
            self.say(f"✗ {out['message']}", cls="msg-err")
            self.start_tutor(None)   # 助教自动纠错讲解（内核仍是唯一裁判）
            return
        if out["kind"] == "ok":
            assert self.entered is not None and self._card is not None
            self._card.update_exercise(self.entered["level"], out["context"])
            self._chat().scroll_end(animate=False)
            return
        # completed
        stars = out["stars"]
        self.say(f"🎉 过关！{'★' * stars}{'☆' * (3 - stars)}", cls="msg-ok")
        self.say(out["output"], cls="msg-dim")
        self.say("标准解（你的路径可能不同，两种都正确）：\n"
                 + "\n".join(out["solution"]), cls="msg-dim")
        for v in out["variants"]:
            self.say(f"💡 变体挑战：{v}", cls="msg-warn")
        self.refresh_sidebar()
        if out.get("world_done"):
            nxt = out.get("next_world")
            self.say("🎉 世界通关！" + (f" 下一站：{nxt} 世界（#game {nxt}）" if nxt
                                      else " 全部世界通关！"), cls="msg-ok")
            self._card = None
            return
        assert out.get("next") is not None
        assert self.entered is not None
        self.entered["level"] = out["next"]
        self.spawn_exercise(out["next"])

    def run_console_command(self, line: str) -> None:
        parts = line.split()
        if line == "#game":
            data = self.engine.rpc("worlds")
            circled = CIRCLED
            lines = []
            for w in data["worlds"]:
                num = circled[w["index"] - 1] if w["index"] <= 11 else str(w["index"])
                lines.append(f"{num} {w['id']} — {w['title']}"
                             f"（{w['done']}/{w['total']} 关）")
            self.say("\n".join(lines) + "\n\n进入：#game <世界>", cls="msg-dim")
            return
        if line.startswith("#game ") and len(parts) >= 2:
            world = parts[1]
            replay = len(parts) > 2 and parts[2] == "replay"
            self.enter_world(world, replay=replay)
            return
        if line.startswith("#check "):
            out = self.engine.rpc("check", expr=line[7:])
        elif line == "#check":
            out = self.engine.rpc("check", expr="Prop")
        elif line.startswith("#reduce "):
            out = self.engine.rpc("reduce", expr=line[8:])
        elif line.startswith("#print "):
            out = self.engine.rpc("print_const", name=line[7:])
        elif line == "#vocab":
            from .vocab import VOCAB, annotate, render_plain
            data = self.engine.rpc("vocab")
            entries = annotate(VOCAB, data["current"],
                               load_world_order(self.engine.repl._worlds_dir()))
            self.say(render_plain(entries), cls="msg-dim")
            return
        elif line == "#env":
            self.say("、".join(self._consts), cls="msg-dim")
            return
        else:
            self.say(f"未知命令 {line}（#check / #reduce / #print / #game）",
                     cls="msg-err")
            return
        if out.get("kind") == "error":
            self.say(out["message"], cls="msg-err")
        else:
            self.say(out.get("output", ""), cls="msg-dim")

    # ---------- 助教（LLM 流式）----------

    def start_tutor(self, question: str | None) -> None:
        if not self.engine.tutor.enabled:
            return
        if self.engine.state != "level":
            self.say("先进入一个世界再问助教", cls="msg-dim")
            return
        state = self.engine.tutor_state(question)
        self.run_worker(self._tutor_job(state), name="tutor",
                        thread=True, exclusive=True, group="tutor")

    def _tutor_job(self, state: dict[str, Any]) -> None:
        """线程 worker：agent 回路——工具轮逐卡透明展示，终答流式。"""
        tutor = self.engine.tutor
        messages = tutor.messages_for(state)
        try:
            for _ in range(4):
                resp = tutor.chat(messages, tools=TOOLS)
                calls = resp.get("tool_calls") or []
                if not calls:
                    self.call_from_thread(
                        self.say_md, resp.get("content") or "(空)")
                    return
                messages.append({"role": "assistant",
                                 "content": resp.get("content") or "",
                                 "tool_calls": calls})
                for tc in calls:
                    fn = tc.get("function", {}).get("name", "")
                    try:
                        args = json.loads(
                            tc.get("function", {}).get("arguments") or "{}")
                    except json.JSONDecodeError:
                        args = {}
                    result = self.engine.exec_tool(fn, args)
                    self.call_from_thread(
                        self.say,
                        f"🔧 {fn}({json.dumps(args, ensure_ascii=False)})\n"
                        f"[dim]{result[:160]}[/]", cls="msg-dim")
                    messages.append({"role": "tool",
                                     "tool_call_id": tc.get("id", ""),
                                     "content": result})
            card = self.call_from_thread(self._tutor_card_open)
            buf = ""
            for delta in tutor.stream(messages):
                buf += delta
                self.call_from_thread(self._tutor_card_update, card, buf)
        except OSError as err:
            self.call_from_thread(self.say,
                                  f"[助教连接中断：{err}]", cls="msg-dim")

    def _tutor_card_open(self) -> Markdown:
        card = Markdown("*🤖 助教思考中…*", classes="msg-dim")
        self._chat().mount(card)
        self._chat().scroll_end(animate=False)
        return card

    def _tutor_card_update(self, card: Markdown, buf: str) -> None:
        card.update(buf)
        self._chat().scroll_end(animate=False)

    # ---------- 动作 ----------

    def action_back(self) -> None:
        if self.engine.state == "level":
            self.engine.rpc("exit_level")
            self.say("[dim]已离开关卡（进度保留，重新进入从本关继续）[/]", cls="msg-dim")
            self.entered = None
            self.refresh_sidebar()

    def action_hint(self) -> None:
        self.run_line("hint")

    def action_solution(self) -> None:
        self.run_line("solution")

    @on(Input.Submitted, "#command-in")
    def on_command(self, event: Input.Submitted) -> None:
        value = event.value
        event.input.value = ""
        self.run_line(value)
