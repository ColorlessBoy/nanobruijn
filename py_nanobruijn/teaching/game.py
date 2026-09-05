"""game 模式：.game 纯文本关卡语言加载器 + 游戏状态机。

世界格式（仿 core.fol 逐行风格，零依赖）：

    world And
    title 合取世界
    intro 开场叙事
    requires: Or              # 课程前置世界（可多个），决定拓扑推荐序
    lesson: <课堂段落，可多个>
    example: <演示关命题>      # 块尾字段：后跟演示解脚本行（同 solution 收集）
    intro a                   # ← 演示脚本行
    exact ha
    using: and                # fol 片段依赖（定义仪式现场加载）
    level 1
    name 关卡名
    goal: <命题（教学语法）>
    hint: <分层提示，可多个>
    ban: <禁用的 tactic 名，可多个>
    solution:
    <标准解脚本行，到 --- / level / 文件尾为止>
    ---
    level 2
    ...

加载：GameLoader().load(path) 单世界；load_all(dir)/load_world_order(dir)
按 requires 拓扑排序（循环/未知前置报错）。存档 profile（resolve_profile）
按次累积在 saves/<profile>/<世界>.json，默认续玩最近活动档。
"""
from __future__ import annotations

import json
import os
import re

KNOWN_TACTICS = ('intro', 'apply', 'exact', 'cases', 'rewrite',
                 'exit', 'context', 'help')

_FIELD_RE = re.compile(r'^([a-zA-Z]+):?\s*(.*)$')


class Level:
    def __init__(self, number: int, name: str, goal: str,
                 hints: list[str], solution: list[str],
                 bans: list[str], variants: list[str] | None = None):
        self.number = number
        self.name = name
        self.goal = goal
        self.hints = hints
        self.solution = solution
        self.bans = bans
        self.variants = variants or []


class Game:
    def __init__(self, world_id: str, title: str, intro: str,
                 levels: list[Level], using: list[str] | None = None, *,
                 requires: list[str] | None = None,
                 lessons: list[str] | None = None,
                 example_goal: str = "",
                 example: list[str] | None = None):
        self.world_id = world_id
        self.title = title
        self.intro = intro
        self.levels = levels
        self.using = using or []
        self.requires = requires or []
        self.lessons = lessons or []
        self.example_goal = example_goal
        self.example = example or []

    def level(self, number: int) -> Level:
        return self.levels[number - 1]


# 世界级字段键（example 脚本行收集的终止符）。
# 'intro' 不在终止集内——它与 tactic `intro x` 撞名，约定 example: 是块尾字段
# （同 solution:），之后只跟 level / --- / 文件尾。
_EXAMPLE_EXIT = {'world', 'title', 'using', 'requires', 'lesson', 'example',
                 'level', 'name', 'goal', 'hint', 'ban', 'variant', 'solution'}


class GameLoader:
    @staticmethod
    def load_all(worlds_dir: str) -> list[Game]:
        """加载目录内全部 .game，按 requires: 拓扑排序返回（循环/未知前置报错）。"""
        import glob
        games = [GameLoader().load(p) for p in sorted(
            glob.glob(os.path.join(worlds_dir, "*.game")))]
        by_id = {g.world_id: g for g in games}
        out: list[Game] = []
        seen: set[str] = set()
        visiting: set[str] = set()

        def visit(g: Game) -> None:
            if g.world_id in seen:
                return
            if g.world_id in visiting:
                raise ValueError(f"game: 世界依赖循环：{g.world_id}")
            visiting.add(g.world_id)
            for r in g.requires:
                if r not in by_id:
                    raise ValueError(
                        f"game: {g.world_id} requires 未知世界 {r!r}")
                visit(by_id[r])
            visiting.discard(g.world_id)
            seen.add(g.world_id)
            out.append(g)

        for g in games:
            visit(g)
        return out

    def load(self, path: str) -> Game:
        with open(path, encoding="utf-8") as f:
            lines = f.read().splitlines()
        world_id = title = intro = ""
        using: list[str] = []
        requires: list[str] = []
        lessons: list[str] = []
        example_goal = ""
        example: list[str] = []
        levels: list[Level] = []
        cur: dict | None = None
        in_solution = False
        in_example = False
        for lineno, line in enumerate(lines, 1):
            stripped = line.strip()
            if not stripped or stripped.startswith('#'):
                continue
            if in_example:
                m = _FIELD_RE.match(stripped)
                if stripped == '---':
                    in_example = False
                    continue
                if m and m.group(1) in _EXAMPLE_EXIT:
                    in_example = False  # 字段行结束收集，落入正常处理
                else:
                    example.append(stripped)
                    continue
            if in_solution:
                if stripped == '---':
                    in_solution = False
                    cur = None
                    continue
                if stripped.startswith('level '):
                    in_solution = False
                else:
                    m = _FIELD_RE.match(stripped)
                    if m and m.group(1) in ('hint', 'ban', 'variant',
                                             'name', 'goal'):
                        in_solution = False  # 字段行结束收集
                    else:
                        cur['solution'].append(stripped)
                        continue
            if stripped == '---':
                cur = None
                continue
            m = _FIELD_RE.match(stripped)
            if m is None:
                raise ValueError(f"game: 无法解析第 {lineno} 行: {stripped!r}")
            key, val = m.group(1), m.group(2).strip()
            if key == 'world':
                world_id = val
            elif key == 'title':
                title = val
            elif key == 'intro':
                intro = val
            elif key == 'using':
                using = [x.strip() for x in val.split(',') if x.strip()]
            elif key == 'requires':
                if cur is not None:
                    raise ValueError(
                        f"game: 第 {lineno} 行 requires 是世界级字段")
                requires = [x.strip() for x in val.split(',') if x.strip()]
            elif key == 'lesson':
                if cur is not None:
                    raise ValueError(
                        f"game: 第 {lineno} 行 lesson 是世界级字段")
                lessons.append(val)
            elif key == 'example':
                if cur is not None:
                    raise ValueError(
                        f"game: 第 {lineno} 行 example 是世界级字段")
                example_goal = val
                example = []
                in_example = True
            elif key == 'level':
                cur = {'number': int(val), 'name': '', 'goal': '',
                       'hints': [], 'solution': [], 'bans': [], 'variants': []}
                levels.append(cur)
            elif cur is None:
                raise ValueError(f"game: 第 {lineno} 行 {key} 在关卡外: {stripped!r}")
            elif key == 'name':
                cur['name'] = val
            elif key == 'goal':
                cur['goal'] = val
            elif key == 'hint':
                cur['hints'].append(val)
            elif key == 'variant':
                cur['variants'].append(val)
            elif key == 'ban':
                if val not in KNOWN_TACTICS:
                    raise ValueError(f"game: 第 {lineno} 行 ban 了未知 tactic {val!r}")
                cur['bans'].append(val)
            elif key == 'solution':
                in_solution = True  # 后续行属于 solution
            else:
                raise ValueError(f"game: 第 {lineno} 行未知字段 {key!r}")
        if not world_id:
            raise ValueError("game: 缺少 world 字段")
        for i, lv in enumerate(levels, 1):
            if not lv['goal']:
                raise ValueError(f"game: level {lv['number']} 缺少 goal")
            if lv['number'] != i:
                raise ValueError(
                    f"game: level 序号不连续（期望 {i}，实际 {lv['number']}）——"
                    f"关卡必须从 1 开始连续编号")
        return Game(world_id, title, intro,
                    [Level(l['number'], l['name'], l['goal'], l['hints'],
                           l['solution'], l['bans'], l['variants'])
                     for l in levels], using,
                    requires=requires, lessons=lessons,
                    example_goal=example_goal, example=example)


def load_world_order(worlds_dir: str) -> list[str]:
    """世界推荐顺序：requires: 拓扑序。"""
    return [g.world_id for g in GameLoader.load_all(worlds_dir)]

SAVES_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), "saves")


class GameSession:
    def __init__(self, game: Game, saves_dir: str | None = None,
                 replay: bool = False):
        self.game = game
        self.saves_dir = saves_dir if saves_dir is not None else SAVES_DIR
        self.stars: dict[int, int] = {}
        self.current_level_no: int | None = None
        # replay 模式：进度视图清零从第 1 关重打；存档写入时与历史最佳取
        # max（只升不降），旧档文件不删不毁
        self._replay = replay
        self._best: dict[int, int] = {}

    def unlocked(self, number: int) -> bool:
        return number == 1 or (number - 1) in self.stars

    def force_level(self, number: int) -> None:
        """#game <世界> <关卡号>：重玩指定关卡（覆盖星级）。"""
        self._forced_level = number

    def advance_after(self, number: int) -> None:
        """直达重玩通关后顺延：下一关存在则强制进入。"""
        if number < len(self.game.levels):
            self._forced_level = number + 1

    def next_unfinished(self) -> int | None:
        forced = getattr(self, '_forced_level', None)
        if forced is not None:
            self._forced_level = None
            self._came_from_force = True
            return forced
        self._came_from_force = False
        for lv in self.game.levels:
            if lv.number not in self.stars:
                return lv.number
        return None

    def complete(self, steps: int, hints_used: int) -> int:
        """通关结算星级：每条 hint 降一星（0 hint → 3★/2★、1 hint → 2★、≥2 → 1★）。

        3★ 容错：步数 ≤ 标准解 + 2（异形等价路径不白打）。
        """
        lv = self.game.level(self.current_level_no or self.next_unfinished())
        stars = 1
        if hints_used <= 1:
            stars = 2
        if hints_used == 0 and steps <= len(lv.solution) + 2:
            stars = 3
        self.stars[lv.number] = stars
        self.save()
        return stars

    def save(self) -> None:
        os.makedirs(self.saves_dir, exist_ok=True)
        path = os.path.join(self.saves_dir, f"{self.game.world_id}.json")
        data = self.stars
        if self._replay:
            data = {k: max(self._best.get(k, 0), v)
                    for k, v in self.stars.items()}
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"stars": {str(k): v for k, v in data.items()}},
                      f, ensure_ascii=False)

    def load_progress(self) -> None:
        path = os.path.join(self.saves_dir, f"{self.game.world_id}.json")
        if not os.path.exists(path):
            return
        try:
            with open(path, encoding="utf-8") as f:
                data = json.load(f)
            stars = data.get("stars", {})
            self.stars = {int(k): v for k, v in stars.items()
                          if isinstance(v, int) and 1 <= v <= 3}
        except (ValueError, TypeError, OSError):
            self.stars = {}  # 损坏存档：重置为空进度（教学工具宽容处理）
        if self._replay:
            self._best = dict(self.stars)
            self.stars = {}


def _latest_file_mtime(path: str) -> float | None:
    """目录内全部文件的最新 mtime（空目录返回 None）。"""
    best: float | None = None
    for dirpath, _dirs, files in os.walk(path):
        for f in files:
            m = os.path.getmtime(os.path.join(dirpath, f))
            if best is None or m > best:
                best = m
    return best


def resolve_profile(root: str, name: str | None = None,
                    new: bool = False) -> str:
    """解析存档 profile 目录（像 sessions/ 一样按次累积、可管理）。

    - name 给定：root/<name>（命名档位，不存在则创建）
    - new=True：新建时间戳 profile（新开一局，旧档全部保留）
    - 默认：续玩最近活动（档内存档文件 mtime 最新）的 profile；
      空档（从未玩过）跳过；一个活动的都没有则新建
    旧版扁平存档（root/*.json）一次性迁移进 root/default/。
    """
    import time
    os.makedirs(root, exist_ok=True)
    entries = sorted(
        e for e in os.listdir(root)
        if os.path.isdir(os.path.join(root, e)))
    if not entries:
        legacy = [e for e in os.listdir(root) if e.endswith(".json")]
        if legacy:
            dst = os.path.join(root, "default")
            os.makedirs(dst, exist_ok=True)
            for f in legacy:
                os.replace(os.path.join(root, f), os.path.join(dst, f))
            entries = ["default"]
    if name:
        path = os.path.join(root, name)
        os.makedirs(path, exist_ok=True)
        return path
    if not new and entries:
        active = [(m, os.path.join(root, e)) for e in entries
                  if (m := _latest_file_mtime(os.path.join(root, e)))
                  is not None]
        if active:
            return max(active, key=lambda t: t[0])[1]
    i = 0
    while True:
        cand = os.path.join(root, time.strftime("%Y%m%d-%H%M%S")
                            + (f"-{i}" if i else ""))
        if not os.path.exists(cand):
            os.makedirs(cand)
            return cand
        i += 1
