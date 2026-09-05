"""Lean 4 词表索引：核心词汇的查询与进度对照（不是教学本体）。

正式教学在对应世界的课堂段落里——kernel 的概念（函数、函数类型、fun、forall）
都是新语言的生词，必须循序渐进地教，不能预设玩家会编程。本表只做两件事：
①复习查询（每个词：读法/一句话意思/最小例子）；②进度对照（学到哪亮到哪）。

纪律：任何词条的 mean 不得使用词表中更晚出现的词。
"""
from __future__ import annotations

VOCAB: list[dict[str, str]] = [
    {"word": "Sort", "read": "直接念 Sort",
     "mean": "给「类型的类型」编级的记号：Sort u 在 Sort (u+1) 里，没有顶层。",
     "example": "#check Prop  →  Prop : Type", "world": "Basic"},
    {"word": "Prop（= Sort 0）", "read": "念 prop",
     "mean": "命题那一类——像「2+2=4」这样可判断真假的句子。",
     "example": "#check True  →  True : Prop", "world": "Basic"},
    {"word": "Type（= Sort 1）", "read": "念 type",
     "mean": "Prop 所在的那一类。",
     "example": "#check Prop  →  Prop : Type", "world": "Basic"},
    {"word": "a : T", "read": "读 a 冒号 T",
     "mean": "a 是项（term），T 是 a 的类型。",
     "example": "#check True.intro  →  True.intro : True", "world": "Basic"},
    {"word": "fun (x : A) => e", "read": "读 fun x 得 e",
     "mean": "造一台机器：收一个叫 x 的输入（: A 是类型注解，必写），吐出 e。",
     "example": "#check fun (h : True) => h", "world": "Basic"},
    {"word": "A -> B", "read": "读 A 到 B",
     "mean": "函数类型——机器的标签：吃一个 A 类的东西，吐出一个 B 类的东西。",
     "example": "#check True -> True  →  True -> True : Prop", "world": "Basic"},
    {"word": "forall (x : A), B", "read": "读 对任取 x",
     "mean": "带名字的箭头链——目标显示里的 ∀ 就是它。",
     "example": "#check forall (h : True), True", "world": "Basic"},
    {"word": "intro x", "read": "读 介绍",
     "mean": "tactic：把目标的下一个输入搬到手边（给 λ 再包一层）。",
     "example": "目标 ? : ∀ (h : True), True → intro h", "world": "Basic"},
    {"word": "exact e", "read": "直接念 exact",
     "mean": "tactic：把手头的项交给内核检查——「就是这个」。",
     "example": "exact True.intro", "world": "Basic"},
    {"word": "apply f", "read": "直接念 apply",
     "mean": "tactic：用一台现成机器反推目标（只接受常量名）。",
     "example": "apply And.intro", "world": "Basic"},
    {"word": "True / True.intro", "read": "念 True",
     "mean": "最平凡的命题：恰有一个证据 True.intro。",
     "example": "#check True.intro  →  True.intro : True", "world": "TrueFalse"},
    {"word": "False / False.rec", "read": "念 False",
     "mean": "没有任何证据的命题；爆炸原理——有 False 的证据则一切成立。",
     "example": "exact @False.rec.{0} (fun (x : False) => a) hf", "world": "TrueFalse"},
    {"word": "And / And.intro / And.left / And.right", "read": "念 And",
     "mean": "合取：证据是一对。intro 成对构造；left/right 取一半。",
     "example": "exact And.right a b h", "world": "And"},
    {"word": "Or / Or.inl / Or.inr", "read": "念 Or",
     "mean": "析取：证据二选一（左路 inl / 右路 inr）。",
     "example": "apply Or.inl", "world": "Or"},
    {"word": "cases h", "read": "读 凯斯",
     "mean": "tactic：对 And/Or/False/Exists 做情形分析——每条路都要走。",
     "example": "cases h as ha hb", "world": "Or"},
    {"word": "Not a", "read": "读 诺特 a",
     "mean": "否定：Not a 就是 a -> False（把证据变成荒谬的机器）。",
     "example": "#check Not", "world": "Not"},
    {"word": "@Exists.{1} α p / Exists.intro", "read": "读 存在",
     "mean": "存在命题：一个证人 w 加上 p w 的证明。",
     "example": "exact @Exists.intro.{1} Prop p a ha", "world": "Exists"},
    {"word": "Iff / Iff.mp / Iff.mpr", "read": "读 当且仅当",
     "mean": "等价：两座桥——mp 从 a 到 b，mpr 从 b 到 a。",
     "example": "apply Iff.intro", "world": "Iff"},
    {"word": "@Eq.{1} Prop p q / Eq.refl / rewrite h", "read": "读 等于",
     "mean": "等式：refl 说任何东西等于自己；rewrite 拿等式替换目标。",
     "example": "exact @Eq.refl.{1} Prop p", "world": "Eq"},
    {"word": "zero / succ / Nat.rec", "read": "succ 念 后继",
     "mean": "自然数：零与后继；Nat.rec 是归纳——第一个真正会计算的消除。",
     "example": "#reduce add two two  →  four", "world": "Nat"},
]


def annotate(entries: list[dict], current_world: str | None,
             order: list[str]) -> list[dict]:
    """按世界拓扑序标注词条状态：done（已学）/ now（当前世界）/ todo（待学）。

    current_world 为玩家所在或推荐进入的世界；None 时视为刚起步。
    """
    cur = order.index(current_world) if current_world in order else -1
    out = []
    for e in entries:
        e = dict(e)
        i = order.index(e["world"]) if e["world"] in order else len(order)
        e["status"] = "done" if i < cur else ("now" if i == cur else "todo")
        out.append(e)
    return out


def render_plain(entries: list[dict]) -> str:
    """REPL 纯文本渲染。"""
    lines = []
    for e in entries:
        mark = {"done": "✓", "now": "●", "todo": "○"}[e["status"]]
        lines.append(f"{mark} {e['word']}  [{e['world']}]")
        lines.append(f"    读法：{e['read']}")
        lines.append(f"    意思：{e['mean']}")
        lines.append(f"    例子：{e['example']}")
    return "\n".join(lines)
