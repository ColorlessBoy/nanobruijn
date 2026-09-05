"""Web 版教学游戏：无头会话引擎 + 零依赖 HTTP 服务。

架构（路线①：Python 服务 + TS 客户端；内核零改动）：
- WebApp：无头状态机——复用 Repl/GameSession/ProofState/run_tactic 全部原语，
  把 REPL 的交互流程（定义仪式 → 课堂 → 演示关 → 关卡循环）转成 JSON 结构
- serve()：stdlib ThreadingHTTPServer；POST /api 为 JSON RPC，GET 供静态文件
- 前端：teaching/web/（TypeScript，esbuild 打包为 web/app.js）

启动：python -m py_nanobruijn web [--port 8765]
"""
from __future__ import annotations

import io
import json
import os
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from .core import make_fresh_core
from .game import GameLoader, GameSession, load_world_order
from .llm import TOOLS, Tutor
from .parser import ParseError, parse_expr
from .proof import ProofState
from .repl import Repl
from .tactics import AbortProof, ProofDone, run_tactic
from .vocab import VOCAB, annotate

try:  # 内核超时（教学层惯例：ValueError 之外的超时类型）
    from ..errors import CheckTimeoutError
except ImportError:  # pragma: no cover
    CheckTimeoutError = ()  # type: ignore[assignment]

WEB_DIR = os.path.join(os.path.dirname(__file__), "web")
STEP_TACTICS = Repl.STEP_TACTICS
DEFAULT_TIMEOUT = 5.0


def note_of(text: str) -> str:
    """从 context() 文本里提取附加注释（如 rewrite 的替换说明）。

    结构化上下文由 ProofState.context_structured() 直接给出，不再解析文本。
    """
    keep = []
    for line in text.splitlines():
        if line.startswith(("上下文: ", "目标: ", "当前项: ", "所有目标")):
            continue
        keep.append(line)
    return "\n".join(line for line in keep if line.strip())


class WebApp:
    """无头会话引擎：一个 WebApp = 一个浏览器会话（含独立 fresh 内核）。"""

    def __init__(self, saves_dir: str | None = None):
        self.repl = Repl(make_fresh_core(), timeout_secs=DEFAULT_TIMEOUT,
                         color=False, saves_dir=saves_dir, fresh=True)
        self.session: GameSession | None = None
        self.state = "main"          # main | level
        self.level_no: int | None = None
        self.steps = 0
        self.hints = 0
        self.proof: ProofState | None = None
        self.tutor = Tutor()
        self.recent: list[str] = []      # 最近的 tactic 行（助教上下文）
        self.last_error = ""

    # ---------- RPC 分发 ----------

    def rpc(self, action: str, **params) -> dict:
        methods = {
            "worlds": lambda: {"kind": "worlds", **self.worlds()},
            "enter_world": self.enter_world,
            "tactic": self.tactic,
            "hint": self.hint,
            "solution": self.solution,
            "exit_level": self.exit_level,
            "check": self.check,
            "print_const": self.print_const,
            "reduce": self.reduce,
            "constants": self.constants,
            "saves": self.saves,
            "ask": self.ask,
            "tutor_status": self.tutor_status,
            "vocab": self.vocab,
        }
        fn = methods.get(action)
        if fn is None:
            return {"kind": "error", "message": f"未知 action: {action!r}"}
        try:
            return fn(**params)
        except Exception as err:  # noqa: BLE001 - RPC 顶层兜底
            return {"kind": "error", "message": f"{type(err).__name__}: {err}"}

    # ---------- 世界列表 / 存档 ----------

    def worlds(self) -> dict:
        d = self.repl._worlds_dir()
        order = load_world_order(d)
        games = {g.world_id: g for g in GameLoader.load_all(d)}
        worlds = []
        for i, wid in enumerate(order, 1):
            g = games[wid]
            s = GameSession(g, saves_dir=self.repl.saves_dir)
            s.load_progress()
            worlds.append({
                "id": wid, "index": i, "title": g.title,
                "requires": g.requires,
                "done": len(s.stars), "total": len(g.levels),
                "stars": [s.stars.get(lv.number, 0) for lv in g.levels],
            })
        profile = os.path.basename(os.path.normpath(self.repl.saves_dir))
        return {"worlds": worlds, "profile": profile}

    def saves(self) -> dict:
        root = self.repl.saves_root
        profiles = sorted(
            (e for e in os.listdir(root)
             if os.path.isdir(os.path.join(root, e))),
            key=lambda e: os.path.getmtime(os.path.join(root, e)),
            reverse=True) if os.path.isdir(root) else []
        cur = os.path.basename(os.path.normpath(self.repl.saves_dir))
        return {"profiles": profiles, "current": cur}

    def _demo_payload(self, game) -> dict:
        """预计算演示关：每一步 tactic 后的目标状态（前端逐行回放）。"""
        st = ProofState(self.repl.core, parse_expr(self.repl.core, game.example_goal),
                        DEFAULT_TIMEOUT, False)
        steps = []
        for line in game.example:
            try:
                out = run_tactic(st, line)
                steps.append({"line": line, "context": st.context_structured(),
                              "note": note_of(out) if out else ""})
            except ProofDone as done:
                steps.append({"line": line, "done": done.text})
                break
        return {"goal": game.example_goal, "steps": steps}

    # ---------- 进入世界 ----------

    def _level_payload(self, no: int) -> dict:
        assert self.session is not None
        lv = self.session.game.level(no)
        return {"number": no, "name": lv.name, "goal": lv.goal,
                "bans": lv.bans, "context": self.proof.context_structured()}

    def enter_world(self, world: str, replay: bool = False,
                    level: int | None = None) -> dict:
        d = self.repl._worlds_dir()
        path = os.path.join(d, world.lower() + ".game")
        if not os.path.exists(path):
            return {"kind": "error",
                    "message": f"未知世界 {world!r}（#game 看列表）"}
        game = GameLoader().load(path)
        session = GameSession(game, saves_dir=self.repl.saves_dir,
                              replay=replay)
        session.load_progress()
        # 定义仪式：真实加载（fresh），文本捕获给前端
        buf = io.StringIO()
        self.repl._definition_ceremony(session, buf)
        no = level if level is not None else session.next_unfinished()
        if no is None:
            return {"kind": "error", "message": "该世界已全部通关"}
        self.session = session
        self.state = "level"
        self.level_no = no
        self.steps = 0
        self.hints = 0
        self.session.current_level_no = no
        lv = game.level(no)
        self.proof = ProofState(self.repl.core, parse_expr(self.repl.core, lv.goal),
                                DEFAULT_TIMEOUT, False)
        return {
            "kind": "entered", "world": world, "title": game.title,
            "intro": game.intro, "definitions": buf.getvalue().strip(),
            "lessons": game.lessons,
            "example": self._demo_payload(game),
            "level": self._level_payload(no),
        }

    # ---------- 关卡循环 ----------

    def _require_level(self) -> dict:
        if self.state != "level" or self.session is None or self.proof is None:
            return {"kind": "error", "message": "不在关卡内（先 #game 进入世界）"}
        return {}

    def tactic(self, line: str) -> dict:
        bad = self._require_level()
        if bad:
            return bad
        assert self.session is not None and self.proof is not None
        lv = self.session.game.level(self.level_no)
        for part in line.split(";"):
            head = part.strip().split(maxsplit=1)[0]
            if head in lv.bans:
                return {"kind": "error",
                        "message": f"本关禁用 {head}——这关故意不给你这条捷径，"
                                   f"换一条路想想（hint 会降星）"}
        is_step = line.strip().split(maxsplit=1)[0] in STEP_TACTICS
        self.recent.append(line)
        del self.recent[:-8]
        try:
            out = run_tactic(self.proof, line)
        except ProofDone as done:
            if is_step:
                self.steps += 1
            stars = self.session.complete(self.steps, self.hints)
            nxt = self.session.next_unfinished()
            resp = {
                "kind": "completed", "output": done.text, "stars": stars,
                "solution": lv.solution, "variants": lv.variants,
                "world": self.session.game.world_id,
                "world_done": nxt is None,
            }
            if nxt is not None:
                self.level_no = nxt
                self.session.current_level_no = nxt
                self.steps = 0
                self.hints = 0
                lv2 = self.session.game.level(nxt)
                self.proof = ProofState(
                    self.repl.core, parse_expr(self.repl.core, lv2.goal),
                    DEFAULT_TIMEOUT, False)
                resp["next"] = self._level_payload(nxt)
            else:
                order = load_world_order(self.repl._worlds_dir())
                try:
                    i = order.index(self.session.game.world_id)
                    resp["next_world"] = (order[i + 1]
                                          if i + 1 < len(order) else None)
                except ValueError:
                    resp["next_world"] = None
                self.state = "main"
            return resp
        except AbortProof:
            return self.exit_level()
        except (ValueError, ParseError, CheckTimeoutError) as err:
            self.last_error = str(err)
            return {"kind": "error", "message": str(err)}
        if is_step:
            self.steps += 1
        return {"kind": "ok", "context": self.proof.context_structured(),
                "note": note_of(out)}

    def hint(self) -> dict:
        bad = self._require_level()
        if bad:
            return bad
        lv = self.session.game.level(self.level_no)
        if self.hints >= len(lv.hints):
            return {"kind": "error", "message": "没有更多提示了——再想想"}
        text = lv.hints[self.hints]
        self.hints += 1
        return {"kind": "hint", "hint": text, "index": self.hints,
                "total": len(lv.hints)}

    def solution(self) -> dict:
        bad = self._require_level()
        if bad:
            return bad
        lv = self.session.game.level(self.level_no)
        return {"kind": "solution", "solution": lv.solution,
                "note": "看过标准解本关不计星——复制练手，或 exit 后从本关重来"}

    def exit_level(self) -> dict:
        bad = self._require_level()
        if bad:
            return bad
        self.state = "main"
        return {"kind": "abandoned",
                "note": "已离开关卡（进度保留，重新进入从本关继续）"}

    # ---------- 自由控制台 ----------

    def check(self, expr: str) -> dict:
        out = self.repl.process_line(f"#check {expr}")
        kind = "error" if out.startswith("error:") else "ok"
        return {"kind": kind, "output": out.removeprefix("error: ").strip()}

    def print_const(self, name: str) -> dict:
        out = self.repl.process_line(f"#print {name}")
        kind = "error" if out.startswith("error:") else "ok"
        return {"kind": kind, "output": out.removeprefix("error: ").strip()}

    def reduce(self, expr: str) -> dict:
        out = self.repl.process_line(f"#reduce {expr}")
        kind = "error" if out.startswith("error:") else "ok"
        return {"kind": kind, "output": out.removeprefix("error: ").strip()}

    def constants(self) -> dict:
        return {"kind": "constants",
                "constants": self.repl.core.constants()}

    def _current_world(self) -> str | None:
        if self.state == "level" and self.session is not None:
            return self.session.game.world_id
        d = self.repl._worlds_dir()
        for wid in load_world_order(d):
            s = GameSession(GameLoader().load(
                os.path.join(d, wid.lower() + ".game")),
                saves_dir=self.repl.saves_dir)
            s.load_progress()
            if s.next_unfinished() is not None:
                return wid
        return None

    def vocab(self) -> dict:
        current = self._current_world()
        order = load_world_order(self.repl._worlds_dir())
        return {"kind": "vocab", "current": current,
                "entries": annotate(VOCAB, current, order)}

    # ---------- 助教（LLM）——内核仍是唯一裁判 ----------

    def tutor_status(self) -> dict:
        return {"kind": "tutor_status", "enabled": self.tutor.enabled,
                "model": self.tutor.model if self.tutor.enabled else None}

    def tutor_state(self, question: str | None = None) -> dict:
        assert self.session is not None and self.proof is not None
        lv = self.session.game.level(self.level_no)
        return {"world": self.session.game.world_id,
                "level": {"number": lv.number, "name": lv.name, "goal": lv.goal},
                "context": self.proof.context_structured(),
                "recent": self.recent[-6:],
                "last_error": self.last_error,
                "question": question}

    def exec_tool(self, name: str, args: dict) -> str:
        """助教 agent 的工具执行：内核真话 + 词表 + 教材（结果原样给 LLM）。"""
        if name == "kernel_check":
            out = self.check(args.get("expr", ""))
            tag = "" if out["kind"] == "ok" else "\n（内核拒绝——据此纠正讲解方向）"
            return out["output"] + tag
        if name == "kernel_reduce":
            out = self.reduce(args.get("expr", ""))
            tag = "" if out["kind"] == "ok" else "\n（内核拒绝）"
            return out["output"] + tag
        if name == "vocab_lookup":
            word = (args.get("word") or "").lower()
            entries = self.vocab()["entries"]
            if word:
                entries = [e for e in entries if word in e["word"].lower()]
            lines = [f"{e['word']} [{e['world']}]：{e['read']}｜{e['mean']}"
                     f"｜例：{e['example']}" for e in entries]
            return "\n".join(lines) or "（词表没有匹配的词）"
        if name == "lesson":
            world = (args.get("world") or "").strip()
            path = os.path.join(self.repl._worlds_dir(),
                                world.lower() + ".game")
            try:
                game = GameLoader().load(path)
            except (OSError, ValueError):
                return f"（未知世界：{world or '（未指定）'}）"
            return "\n\n".join(
                f"【段{i + 1}】{p}" for i, p in enumerate(game.lessons)
            ) or "（该世界暂无课堂）"
        return f"（未知工具：{name}）"

    def ask(self, question: str = "") -> dict:
        """向助教提问：agent 回路——LLM 可调用内核/词表/教材工具。

        非流式（TUI 客户端自己走流式回路）；trace 是工具调用记录
        （Web 端折叠展示，TUI 端逐卡展示——调用对玩家透明）。
        """
        if not self.tutor.enabled:
            return {"kind": "error",
                    "message": "助教未启用：设置环境变量 NANOBRUIJN_LLM_KEY"
                               "（OpenAI 兼容 API）后可用"}
        if self.state != "level" or self.session is None or self.proof is None:
            return {"kind": "error", "message": "不在关卡内（先进入世界）"}
        messages = self.tutor.messages_for(self.tutor_state(question))
        trace: list[dict] = []
        try:
            md = self._agent_loop(messages, trace)
        except OSError as err:
            return {"kind": "error", "message": str(err)}
        return {"kind": "tutor", "md": md, "trace": trace}

    def _agent_loop(self, messages: list[dict], trace: list[dict]) -> str:
        """最多 4 轮工具调用，最后强制出一段散文讲解。"""
        for _ in range(4):
            resp = self.tutor.chat(messages, tools=TOOLS)
            calls = resp.get("tool_calls") or []
            if not calls:
                return resp.get("content") or ""
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
                result = self.exec_tool(fn, args)
                trace.append({"tool": fn, "args": args, "result": result})
                messages.append({"role": "tool",
                                 "tool_call_id": tc.get("id", ""),
                                 "content": result})
        messages.append({"role": "user",
                         "content": "（工具轮次已用完）请基于以上结果直接给出讲解。"})
        return self.tutor.chat(messages, tools=None).get("content") or ""


# ---------- HTTP 层（stdlib，零依赖） ----------

class _Handler(BaseHTTPRequestHandler):
    server: WebHTTPServer

    def do_GET(self) -> None:
        name = "index.html" if self.path in ("/", "") else self.path.lstrip("/")
        path = os.path.join(WEB_DIR, name)
        if not os.path.isfile(path) or ".." in name:
            self.send_error(404)
            return
        ctype = {"html": "text/html; charset=utf-8",
                 "js": "text/javascript; charset=utf-8",
                 "css": "text/css; charset=utf-8"}.get(name.rsplit(".", 1)[-1],
                                                       "application/octet-stream")
        with open(path, "rb") as f:
            body = f.read()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_POST(self) -> None:
        if self.path != "/api":
            self.send_error(404)
            return
        length = int(self.headers.get("Content-Length", 0))
        try:
            req = json.loads(self.rfile.read(length))
            result = self.server.app.rpc(req.get("action", ""),
                                         **req.get("params", {}))
        except Exception as err:  # noqa: BLE001
            result = {"kind": "error", "message": f"{type(err).__name__}: {err}"}
        body = json.dumps(result, ensure_ascii=False).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, *args) -> None:  # 静默访问日志
        pass


class WebHTTPServer(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, addr, app: WebApp):
        super().__init__(addr, _Handler)
        self.app = app


def serve(host: str = "127.0.0.1", port: int = 8765,
          saves_dir: str | None = None, open_browser: bool = True) -> None:
    """启动 Web 服务（阻塞）。"""
    import webbrowser
    app = WebApp(saves_dir=saves_dir)
    httpd = WebHTTPServer((host, port), app)
    url = f"http://{host}:{port}"
    print(f"nanobruijn web: {url}  （Ctrl-C 退出）")
    if open_browser:
        webbrowser.open(url)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n再见。")
