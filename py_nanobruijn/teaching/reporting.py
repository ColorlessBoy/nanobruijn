"""学习报告与问题上报：做题过程的结构化记录。

数据层 LearningLog 由 repl 接线（每关 start_level → record×N → finish/abandon），
退出时生成学习报告（markdown，reports/），卡住时询问上报（feedback/ JSON）。
全部本地文件，不自动上传（教学工具离线定位）。
"""
from __future__ import annotations

import json
import os
import time


class LearningLog:
    """一次 REPL 会话的做题过程记录。"""

    def __init__(self, fresh: bool):
        self.fresh = fresh
        self.entries: list[dict] = []
        self.current: dict | None = None
        self._t0 = time.time()

    # ---------- 采集（repl 接线） ----------

    def start_level(self, world: str, level: int, name: str, goal: str) -> None:
        self.current = {
            "world": world, "level": level,
            "name": name, "goal": goal,
            "steps": [], "hints": 0, "stars": None,
            "t_start": time.time(),
        }

    def record(self, line: str, error: str | None = None) -> None:
        if self.current is not None:
            self.current["steps"].append((line, error))

    def record_error(self, error: str) -> None:
        """把错误标记到最后一条记录上（repl 在 run_tactic 抛异常后调用）。"""
        if self.current is not None and self.current["steps"]:
            line, _ = self.current["steps"][-1]
            self.current["steps"][-1] = (line, error)

    def hint_used(self) -> None:
        if self.current is not None:
            self.current["hints"] += 1

    def finish_level(self, stars: int) -> None:
        if self.current is not None:
            self.current["stars"] = stars
            self.current["t_end"] = time.time()
            self.entries.append(self.current)
            self.current = None

    def abandon(self) -> None:
        if self.current is not None:
            if self.current["steps"] or self.current["hints"]:
                self.current["t_end"] = time.time()
                self.entries.append(self.current)
            # 空关卡（纯路过）：丢弃
            self.current = None

    # ---------- 产出 ----------

    def has_errors(self) -> bool:
        return any(err for e in self.entries for (_, err) in e["steps"])

    def _stars_str(self, stars: int | None) -> str:
        return f"{'★' * stars}{'☆' * (3 - stars)}" if stars else "未通关"

    def to_markdown(self) -> str:
        lines = ["# nanobruijn 学习报告", ""]
        mode = "fresh（从空环境开始，现场定义）" if self.fresh else "全量环境"
        lines.append(f"- 时间：{time.strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"- 模式：{mode}")
        worlds = sorted({e["world"] for e in self.entries})
        lines.append(f"- 世界：{'、'.join(worlds) or '（无）'}")
        lines.append("")
        lines.append("## 进度")
        lines.append("")
        lines.append("| 世界 | 关卡 | 星级 | 步数 | 提示 |")
        lines.append("|---|---|---|---|---|")
        for e in self.entries:
            tactics = sum(1 for (l, _) in e["steps"]
                          if l.split(maxsplit=1)[0] in
                          ("intro", "apply", "exact", "cases", "rewrite"))
            lines.append(f"| {e['world']} | {e['level']} {e['name']} "
                         f"| {self._stars_str(e['stars'])} "
                         f"| {tactics} | {e['hints']} |")
        lines.append("")
        lines.append("## 关卡回放")
        for e in self.entries:
            stars = self._stars_str(e["stars"])
            lines.append("")
            lines.append(f"### {e['world']} 第 {e['level']} 关："
                         f"{e['name']}（{stars}）")
            lines.append(f"- 目标：`{e['goal']}`")
            lines.append("```text")
            for (line, err) in e["steps"]:
                if err:
                    short = err if len(err) <= 70 else err[:67] + "..."
                    lines.append(f"❌ {line}    → {short}")
                else:
                    lines.append(line)
            lines.append("```")
        pain = self._pain_points()
        if pain:
            lines.append("")
            lines.append("## 你的卡点")
            for (kind, n) in pain:
                lines.append(f"- 「{kind}」出现 {n} 次")
            hinted = [e for e in self.entries if e["hints"]]
            if hinted:
                where = "、".join(f"{e['world']} 第 {e['level']} 关"
                                  for e in hinted)
                lines.append(f"- 使用了提示：{where}")
        return "\n".join(lines) + "\n"

    def _pain_points(self) -> list[tuple[str, int]]:
        counts: dict[str, int] = {}
        for e in self.entries:
            for (_, err) in e["steps"]:
                if not err:
                    continue
                msg = err.removeprefix("error: ")
                kind = msg.split("：")[0].split(":")[0].strip()
                counts[kind] = counts.get(kind, 0) + 1
        return sorted(counts.items(), key=lambda kv: -kv[1])[:5]

    def save_report(self, reports_dir: str) -> str:
        os.makedirs(reports_dir, exist_ok=True)
        path = os.path.join(
            reports_dir,
            time.strftime("%Y%m%d-%H%M%S") + "-learning.md")
        with open(path, "w", encoding="utf-8") as f:
            f.write(self.to_markdown())
        return path

    # ---------- 问题上报 ----------

    def last_error_context(self) -> dict:
        """最近一次错误及其上下文（上报内容；含未结算的当前关）。"""
        candidates = list(self.entries)
        if self.current is not None:
            candidates.append(self.current)
        for e in reversed(candidates):
            for (line, err) in reversed(e["steps"]):
                if err:
                    return {"world": e["world"], "level": e["level"],
                            "name": e["name"], "goal": e["goal"],
                            "input": line, "error": err}
        return {}

    def save_feedback(self, feedback_dir: str, note: str) -> str:
        os.makedirs(feedback_dir, exist_ok=True)
        data = {"time": time.strftime("%Y-%m-%d %H:%M:%S"),
                "note": note, **self.last_error_context()}
        path = os.path.join(
            feedback_dir, time.strftime("%Y%m%d-%H%M%S") + "-feedback.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        return path
