"""game 模式：.game 纯文本关卡语言加载器 + 游戏状态机。

关卡格式（仿 core.fol 逐行风格，零依赖）：

    world And
    title 合取世界
    intro 开场叙事
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
"""
from __future__ import annotations

import json
import os
import re

KNOWN_TACTICS = ('intro', 'apply', 'exact', 'cases', 'done',
                 'abort', 'context', 'help')

_FIELD_RE = re.compile(r'^([a-zA-Z]+):?\s*(.*)$')


class Level:
    def __init__(self, number: int, name: str, goal: str,
                 hints: list[str], solution: list[str],
                 bans: list[str]):
        self.number = number
        self.name = name
        self.goal = goal
        self.hints = hints
        self.solution = solution
        self.bans = bans


class Game:
    def __init__(self, world_id: str, title: str, intro: str,
                 levels: list[Level]):
        self.world_id = world_id
        self.title = title
        self.intro = intro
        self.levels = levels

    def level(self, number: int) -> Level:
        return self.levels[number - 1]


class GameLoader:
    def load(self, path: str) -> Game:
        with open(path, encoding="utf-8") as f:
            lines = f.read().splitlines()
        world_id = title = intro = ""
        levels: list[Level] = []
        cur: dict | None = None
        in_solution = False
        for lineno, line in enumerate(lines, 1):
            stripped = line.strip()
            if not stripped or stripped.startswith('#'):
                continue
            if in_solution:
                if stripped == '---':
                    in_solution = False
                    cur = None
                    continue
                if stripped.startswith('level '):
                    in_solution = False
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
            elif key == 'level':
                cur = {'number': int(val), 'name': '', 'goal': '',
                       'hints': [], 'solution': [], 'bans': []}
                levels.append(cur)
            elif cur is None:
                raise ValueError(f"game: 第 {lineno} 行 {key} 在关卡外: {stripped!r}")
            elif key == 'name':
                cur['name'] = val
            elif key == 'goal':
                cur['goal'] = val
            elif key == 'hint':
                cur['hints'].append(val)
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
        for lv in levels:
            if not lv['goal']:
                raise ValueError(f"game: level {lv['number']} 缺少 goal")
        return Game(world_id, title, intro,
                    [Level(l['number'], l['name'], l['goal'], l['hints'],
                           l['solution'], l['bans']) for l in levels])

SAVES_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), "saves")


class GameSession:
    def __init__(self, game: Game, saves_dir: str | None = None):
        self.game = game
        self.saves_dir = saves_dir if saves_dir is not None else SAVES_DIR
        self.stars: dict[int, int] = {}
        self.current_level_no: int | None = None

    def unlocked(self, number: int) -> bool:
        return number == 1 or (number - 1) in self.stars

    def next_unfinished(self) -> int | None:
        for lv in self.game.levels:
            if lv.number not in self.stars:
                return lv.number
        return None

    def complete(self, steps: int, used_hint: bool) -> int:
        lv = self.game.level(self.current_level_no or self.next_unfinished())
        stars = 1
        if not used_hint:
            stars = 2
        if not used_hint and steps <= len(lv.solution):
            stars = 3
        self.stars[lv.number] = stars
        self.save()
        return stars

    def save(self) -> None:
        os.makedirs(self.saves_dir, exist_ok=True)
        path = os.path.join(self.saves_dir, f"{self.game.world_id}.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"stars": {str(k): v for k, v in self.stars.items()}},
                      f, ensure_ascii=False)

    def load_progress(self) -> None:
        path = os.path.join(self.saves_dir, f"{self.game.world_id}.json")
        if not os.path.exists(path):
            return
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        self.stars = {int(k): v for k, v in data.get("stars", {}).items()}
