"""助教层：接入 OpenAI 兼容 LLM API（DeepSeek/OpenAI/Moonshot/ollama 等均可）。

铁律：内核是唯一裁判——LLM 永远不判定证明对错，只做苏格拉底式提示与概念补充。
零依赖：stdlib urllib 流式（SSE）。

配置（环境变量）：
- NANOBRUIJN_LLM_KEY    （必需；也回退读 DEEPSEEK_API_KEY / OPENAI_API_KEY）
- NANOBRUIJN_LLM_BASE_URL（默认 https://api.deepseek.com）
- NANOBRUIJN_LLM_MODEL   （默认 deepseek-chat）
"""
from __future__ import annotations

import json
import os
import urllib.error
import urllib.request
from collections.abc import Iterator

DEFAULT_BASE = "https://api.deepseek.com"
DEFAULT_MODEL = "deepseek-chat"

SYSTEM_PROMPT = """你是 nanobruijn 证明游戏的助教。这是一个类型论证明闯关游戏：
玩家用 tactic（intro / apply / exact / cases / rewrite）在一个真实内核上写证明，
内核是唯一裁判——你永远不能判定玩家对错，只做提示、解释与鼓励。

你可以调用工具，且调用过程对玩家透明（他们看得到你查了什么、跑了什么）：
- kernel_check / kernel_reduce：教任何概念前，先在真实内核里验证你的例子——
  以内核输出为准，不要凭记忆编造类型。
- vocab_lookup：查单词表（词/读法/意思/例子/学没学），保持教学口径一致。
- lesson：取某个世界的课堂段落作为教材。

规则：
1. 苏格拉底式：绝不主动给完整证明；最多指出下一步该用哪个 tactic 的名字、往哪个方向想。
2. 玩家是零基础学生，只会这些已教概念：类型、项、Sort 阶梯（Sort 0 = Prop，Sort 1 = Type）、
   命题即证据的类型、机器（λ 表达式）、函数类型 A -> B、 forall 起名、
   intro/exact/apply/cases/rewrite。不要用更高深的术语（柯里化、Π 类型、宇宙多态等）。
3. 中文，Markdown 短段落（≤8 行），术语第一次出现用一句话解释。
4. 你的话不改变内核判定；星级与进度只由内核决定。提醒玩家"再试一次"比给答案更有价值。"""


TOOLS = [
    {"type": "function", "function": {
        "name": "kernel_check",
        "description": "在真实内核里检查一个表达式的类型（教学演示前先用它验证）",
        "parameters": {"type": "object", "properties": {
            "expr": {"type": "string", "description": "教学语法表达式"}},
            "required": ["expr"]}}},
    {"type": "function", "function": {
        "name": "kernel_reduce",
        "description": "在真实内核里归约一个表达式（iota 计算演示）",
        "parameters": {"type": "object", "properties": {
            "expr": {"type": "string"}}, "required": ["expr"]}}},
    {"type": "function", "function": {
        "name": "vocab_lookup",
        "description": "查单词表（词/读法/意思/例子/学没学）",
        "parameters": {"type": "object", "properties": {
            "word": {"type": "string", "description": "可选：只查包含该字样的词"}}}}},
    {"type": "function", "function": {
        "name": "lesson",
        "description": "取某个世界的课堂段落（已教概念的教材）",
        "parameters": {"type": "object", "properties": {
            "world": {"type": "string", "description": "世界 id，如 Basic"}},
            "required": ["world"]}}},
]


class Tutor:
    """LLM 助教客户端（OpenAI 兼容 /chat/completions，工具调用 + SSE 流式）。"""

    def __init__(self) -> None:
        self.base = os.environ.get(
            "NANOBRUIJN_LLM_BASE_URL", DEFAULT_BASE).rstrip("/")
        self.model = os.environ.get("NANOBRUIJN_LLM_MODEL", DEFAULT_MODEL)
        self.key = (os.environ.get("NANOBRUIJN_LLM_KEY")
                    or os.environ.get("DEEPSEEK_API_KEY")
                    or os.environ.get("OPENAI_API_KEY") or "")

    @property
    def enabled(self) -> bool:
        return bool(self.key)

    def messages_for(self, state: dict) -> list[dict]:
        """内核提供的局面 → LLM 消息序列。"""
        parts = [f"当前局面（内核提供，一切以此为准）：\n{json.dumps(state, ensure_ascii=False)}"]
        q = state.get("question")
        parts.append(f"玩家的问题：{q}" if q else
                     "玩家刚被内核拒绝（见 last_error）。"
                     "请解释发生了什么、指出方向，但不要给完整证明。")
        return [{"role": "system", "content": SYSTEM_PROMPT},
                {"role": "user", "content": "\n\n".join(parts)}]

    def chat(self, messages: list[dict],
             tools: list[dict] | None = None) -> dict:
        """非流式一轮（支持工具调用）。返回 {"content", "tool_calls"}。"""
        body: dict = {"model": self.model, "messages": messages,
                      "max_tokens": 600, "temperature": 0.4}
        if tools:
            body["tools"] = tools
        req = urllib.request.Request(
            f"{self.base}/chat/completions",
            data=json.dumps(body).encode("utf-8"),
            headers={"Authorization": f"Bearer {self.key}",
                     "Content-Type": "application/json"})
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                data = json.loads(resp.read().decode("utf-8", "replace"))
        except urllib.error.URLError as err:
            raise OSError(f"LLM API 连接失败：{err}") from None
        msg = data["choices"][0]["message"]
        return {"content": msg.get("content"),
                "tool_calls": msg.get("tool_calls") or []}

    def stream(self, messages: list[dict]) -> Iterator[str]:
        """流式返回增量文本（SSE）。网络/协议错误抛 OSError/ValueError。"""
        req = urllib.request.Request(
            f"{self.base}/chat/completions",
            data=json.dumps({"model": self.model, "messages": messages,
                             "stream": True, "max_tokens": 600,
                             "temperature": 0.4}).encode("utf-8"),
            headers={"Authorization": f"Bearer {self.key}",
                     "Content-Type": "application/json"})
        try:
            resp = urllib.request.urlopen(req, timeout=60)
        except urllib.error.URLError as err:
            raise OSError(f"LLM API 连接失败：{err}") from None
        with resp:
            for raw in resp:
                line = raw.decode("utf-8", "replace").strip()
                if not line.startswith("data:"):
                    continue
                payload = line[5:].strip()
                if payload == "[DONE]":
                    return
                try:
                    delta = json.loads(payload)["choices"][0]["delta"]
                except (json.JSONDecodeError, KeyError, IndexError):
                    continue
                content = delta.get("content")
                if content:
                    yield content

    def complete(self, messages: list[dict]) -> str:
        return "".join(self.stream(messages))
