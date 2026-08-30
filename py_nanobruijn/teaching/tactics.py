from __future__ import annotations

from .proof import ProofState


class AbortProof(Exception):
    """abort：放弃本次证明，返回主循环。"""


class ProofDone(Exception):
    """done 成功：携带完整证明项文本，repl 打印后退出证明子循环。"""

    def __init__(self, text: str):
        super().__init__(text)
        self.text = text


TACTIC_HELP = (
    "tactic（草稿模式）:\n"
    "  intro [x ...]   目标为函数类型时引入 binder（可连写，如 intro a b）\n"
    "  apply <f>       用常量 f 匹配目标；隐式参数自动填充，显式参数变为新目标\n"
    "  exact <e>       当前目标用表达式 e 精确填充（内核检查 e : 目标）\n"
    "  done            全部目标填充后合成证明项并做内核检查\n"
    "  context         重显当前状态\n"
    "  abort           放弃本次证明，返回主循环\n"
    "  help            显示本帮助\n"
)


def run_tactic(state: ProofState, line: str) -> str:
    """执行一行 tactic（可用 `;` 分隔多个）。

    返回展示文本；`done` 抛 ProofDone；`abort` 抛 AbortProof；
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
    if head == "done":
        raise ProofDone(state.done())
    if head == "abort":
        raise AbortProof()
    if head == "context":
        return state.context()
    if head == "help":
        return TACTIC_HELP
    raise ValueError(f"unknown tactic {head!r}（try help）")