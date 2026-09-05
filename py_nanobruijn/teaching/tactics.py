from __future__ import annotations

from .proof import ProofState


class AbortProof(Exception):
    """exit：放弃本次证明，返回主循环（主 REPL 中则退出程序）。"""


class ProofDone(Exception):
    """收工信号：全部目标填充后自动触发，携带内核检查通过的证明项文本。"""

    def __init__(self, text: str):
        super().__init__(text)
        self.text = text


TACTIC_HELP = (
    "tactic（草稿模式）:\n"
    "  intro [x ...]   目标为函数类型时引入 binder（可连写，如 intro a b）\n"
    "  apply <f>       用常量 f 匹配目标；隐式参数自动填充，显式参数变为新目标\n"
    "  cases <h>       对上下文变量 h 做情形分析（And/Or/False/Exists → rec 分解）\n"
    "  rewrite <h>     h : a = b 时把目标中所有 a 替换为 b（Eq.rec 自动应用）\n"
    "  exact <e>       当前目标用表达式 e 精确填充（内核检查 e : 目标）\n"
    "  context         重显当前状态\n"
    "  exit            放弃本次证明，返回主循环（主 REPL 中则退出程序）\n"
    "  help            显示本帮助\n"
)


def run_tactic(state: ProofState, line: str) -> str:
    """执行一行 tactic（可用 `;` 分隔多个）。

    返回展示文本；全部目标填充时自动收工抛 ProofDone；`exit` 抛 AbortProof；
    tactic 错误抛 ValueError / ParseError（repl 捕获后打印并继续）。
    """
    parts = [p.strip() for p in line.split(";") if p.strip()]
    if not parts:
        return ""
    out = ""
    for part in parts:
        result = _run_one(state, part)
        if result:
            out = result
        if state.is_complete():
            raise ProofDone(state.done())  # 最后一发自动收工 + 内核检查
    return out


def _run_one(state: ProofState, line: str) -> str:
    parts = line.split(maxsplit=1)
    head = parts[0]
    rest = parts[1].strip() if len(parts) > 1 else ""
    if head == "intro":
        return state.intro(rest or None)
    if head == "apply":
        if not rest:
            raise ValueError("apply: 缺少常量名（如 apply And.intro）")
        return state.apply(rest)
    if head == "exact":
        if not rest:
            raise ValueError("exact: 缺少表达式（如 exact ha）")
        return state.exact(rest)
    if head == "cases":
        if not rest:
            raise ValueError("cases: 缺少上下文变量（如 cases h）")
        parts = rest.split()
        names = parts[2:] if len(parts) > 2 and parts[1] == "as" else None
        if len(parts) > 1 and parts[1] != "as":
            raise ValueError("cases: 语法为 `cases h` 或 `cases h as a b`")
        return state.cases(parts[0], names)
    if head == "rewrite":
        if not rest:
            raise ValueError("rewrite: 缺少等式前提（如 rewrite h）")
        return state.rewrite(rest)
    if head == "exit":
        raise AbortProof()
    if head == "context":
        return state.context()
    if head == "help":
        return TACTIC_HELP
    raise ValueError(f"unknown tactic {head!r}（try help）")