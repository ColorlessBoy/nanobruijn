# GAME 模式设计：关卡闯关式教学 + opencode skill 集成

日期：2026-08-31
状态：已批准（头脑风暴确认）

> **实施后注记（superseded 偏差，均为设计迭代）**：
> ① 星级规则改为"每条 hint 降一星 + 3★ 容错 +2 步"（学生实测反馈）；
> ② `#game` 无参显示 usage（进度走 `#worlds`）；③ 关卡定位用 REPL 内
> `#game <世界> <关卡号>`（spec 的 `--level` CLI 参数未实现）；
> ④ Combo L2 升级为 Iff 全量版；⑤ 新增 Hard/Eq 世界（"公里"叙事扩展）、
> rewrite tactic、`variant:` 字段——见 tutorials/prove-playbook.md 与 AGENTS.md。

## 1. 背景与目标

当前教学 REPL 已有 `#prove` tactic 草稿模式（ProofState + intro/apply/exact/
done/cases/abort），教学剧本在 `tutorials/prove-playbook.md`（15 剧本三节路径）。
问题：

1. **逻辑词练习不足**——And/Or/Not/Exists/Iff 各逻辑词的练习没有系统覆盖
2. **playbook 定位不清**——markdown 剧本与 REPL 功能脱节，老师加题成本高
3. **AI 无法驱动 REPL**——`repl` 是交互式，agent 不能批量验证/批改

目标：

- 新增 **GAME 模式**：关卡闯关式教学（世界 = 逻辑词主题 → 关卡 = 命题），
  纯文本 `.game` 数据格式，REPL 支持 `#game` 加载与游玩
- **playbook.md 重新定位**为游戏设计文档（md 与 `.game` 双向对照）
- **opencode skill 集成**：AI agent 能驱动 REPL（验证/批改/出题）

## 2. GAME 数据结构（纯文本 `.game` 格式）

### 2.1 文件布局

```
py_nanobruijn/worlds/
  and.game  or.game  not.game  exists.game  iff.game  combo.game
```

### 2.2 格式（仿 core.fol 逐行解析，零依赖）

```
world And
title 合取世界：从构造到分解
intro 你现在要掌握 And 的两个方向：构造它（And.intro）与拆开它（cases）。
level 1
name 初见合取
goal: forall (a : Prop), forall (b : Prop), a -> b -> And a b
hint: 目标头部是 And —— 先 apply And.intro
hint: 剩下两个子目标 a 和 b，intro 引入假设后 exact
solution:
intro a
intro b
apply And.intro
exact h1
exact h2
---
level 2
...
```

字段定义：

| 字段 | 出现次数 | 说明 |
|---|---|---|
| `world` | 1 | 世界标识（And/Or/Not/Exists/Iff/Combo），须与文件名一致 |
| `title` | 1 | 世界标题 |
| `intro` | 1 | 世界开场叙事（进入世界时显示） |
| `level N` | 多 | 关卡分隔符，N 为序号（1 起） |
| `name` | 每关 1 | 关卡名（显示与存档用） |
| `goal:` | 每关 1 | 命题（教学语法，与 `#prove` 同语法） |
| `hint:` | 每关 0..多 | 分层提示，`hint` 命令按序显示 |
| `solution:` | 每关 0..1 | 标准解脚本（多行，到下一个 `---` 或 `level` 为止）；通关后展示 |
| `ban:` | 每关 0..多 | 禁用的 tactic 名（如 `cases`） |

关卡分隔：`---`（可省略，`level N` 本身就分隔）。`solution:` 行之后到
`---`/`level`/文件尾之间的行都是标准解脚本。

### 2.3 解析器（`teaching/game.py`）

仿 `fol.py` 的逐行状态机：

```
GameLoader.load(path) -> Game
Game:  world_id, title, intro, levels: list[Level]
Level: number, name, goal: str, hints: list[str],
       solution: list[str], bans: list[str]
```

错误处理：缺 `goal`/`world` 抛 `ValueError`（与 teaching 层约定一致）；
`ban` 名字不在已知 tactic 集（intro/apply/exact/done/cases/abort）时报错。

## 3. 游戏状态机（`teaching/game.py`）

### 3.1 组件

```
GameSession:
  game: Game
  current_level: int
  stars: dict[int, int]      # level -> 1..3 星
  used_hint: bool            # 当前关卡是否用过 hint
  steps: int                 # 当前关卡 tactic 步数
  banned: set[str]           # 当前关卡禁用 tactic
```

- `GameSession.enter(level)`：进入关卡 → 启动现有 `#prove` 子循环
  （ProofState 复用，教学叙事延续）
- **步数计数**：每个 tactic 命令（intro/apply/exact/cases）计 1 步；
  `hint`/`solution`/`quit`/`abort` 不计步
- 关卡内命令：
  - `hint`：逐条显示提示（首次调用标记 used_hint）
  - `solution`：放弃后看标准解（视为未通关？不——显示解但**不计星**）
  - 其余 tactic 命令走现有 `process_line` 的 `#prove` 通道
- `ban` 生效位置：tactics 分发前检查（ban 的 tactic 报"本关禁用 cases，
  想想 apply/exact 怎么构造"）

### 3.2 通关与星级

- **通关判定**：`done` 时无剩余洞 + 内核检查通过（与标准解不做 def_eq
  比对——binder 名差异会误判，只作展示）
- **星级**：
  - 1 星：通关
  - 2 星：通关且没用过 `hint`
  - 3 星：2 星且 `steps <= len(solution)`（步数不劣于标准解）
- **解锁**：`level N+1` 需 `level N` 通关；通关后自动展示标准解
  （"看看标准解：你的路径和它可能不同，两种都正确"）

### 3.3 存档（`py_nanobruijn/saves/`）

```
saves/<game>-<world>.json:  {"level": 3, "stars": {"1": 3, "2": 2, ...}}
```

- 按世界存档（每世界一个文件）；`saves/` 加入 `.gitignore`（仿 sessions/）
- 存档读写封装在 game.py（`load_progress`/`save_progress`）

## 4. REPL 集成（`teaching/repl.py` + `__main__.py`）

新增命令（主循环层，仿 `#prove` 的 `_ProveSession` 信号机制）：

| 命令 | 行为 |
|---|---|
| `#worlds` | 列出所有可用世界（名字 + 标题 + 星级） |
| `#game` | 无参：当前世界进度；`#game <世界>`：进入世界（显示 intro，进入第一个未通关关卡） |
| 关卡内 `hint` | 下一条提示 |
| 关卡内 `solution` | 放弃当前关卡，显示标准解，返回世界菜单（本关不计星） |
| 关卡内 `quit` | 回到主循环（进度已存档） |

实现方式：新增 `_GameSession` 信号 + `run()` 捕获（与 `_ProveSession`
同模式）；关卡内证明子循环复用 `_prove_loop`（提取为公共方法，加
ban/hint/step 计数包装）。

`__main__.py` 增加 `--game <世界>` 参数：启动 REPL 直接进入指定世界。

## 5. 世界内容（6 世界 × 5 关）

关卡设计原则：每世界 5 关递进——**构造关**（掌握该词的引入规则）→
**组合关**（与已有词混用）→ **结构关**（交换/结合律等）→ **矛盾关**
（与 Not/False 交互）→ **反向关**（从结论反推，Iff/Exists 方向练习）。

### 5.1 And 世界

| 关 | 命题 | 教学点 |
|---|---|---|
| 1 | `a -> b -> And a b` | And.intro 构造 |
| 2 | `And a b -> b` | And.right 投影（或用 cases） |
| 3 | `And (And a b) c -> And a (And b c)` | 合取结合律，嵌套分解 |
| 4 | `And a b -> And b a` | 交换律（已有 and_comm，作为练习） |
| 5 | `Not a -> Not (And a b)` | And 与 Not 的交互（矛盾） |

### 5.2 Or 世界

| 关 | 命题 | 教学点 |
|---|---|---|
| 1 | `a -> Or a b` | Or.inl |
| 2 | `b -> Or a b` | Or.inr |
| 3 | `Or a b -> (a -> c) -> (b -> c) -> c` | Or.rec 本质（cases 体验消去；apply 不支持 recursor 头部，这是已知限制） |
| 4 | `Or a b -> Or b a` | 交换律（cases 双分支） |
| 5 | `Or a b -> Not a -> b` | Or 消去 + 矛盾 |

### 5.3 Not 世界

| 关 | 命题 | 教学点 |
|---|---|---|
| 1 | `(a -> False) -> Not a` | Not 的定义（def 展开） |
| 2 | `a -> Not (Not a)` | 双重否定引入 |
| 3 | `Not (Not (Not a)) -> Not a` | 三重否定弱化（手写，非 mt） |
| 4 | `(a -> b) -> Not b -> Not a` | 逆否（mt 手写） |
| 5 | `Not (Or a b) -> Not a` | Not 与 Or 交互（cases + 矛盾） |

### 5.4 Exists 世界

| 关 | 命题 | 教学点 |
|---|---|---|
| 1 | `@Exists.{1} Prop (fun (x : Prop) => x) -> True` | 简单 witness + 分解 |
| 2 | `forall (p : Prop -> Prop), forall (q : Prop -> Prop), forall (h : forall (x : Prop), p x -> q x), @Exists.{1} Prop p -> @Exists.{1} Prop q` | Exists.imp 方向一（witness 传递） |
| 3 | `forall (p : Prop -> Prop), (forall (x : Prop), p x -> False) -> @Exists.{1} Prop p -> False` | not_exists 方向（矛盾） |
| 4 | `forall (p : Prop -> Prop), @Exists.{1} Prop (fun (x : Prop) => p x) -> @Exists.{1} Prop p` | eta 冗余（witness 结构） |
| 5 | `forall (p : Prop -> Prop), forall (a : Prop), @Exists.{1} Prop p -> p a -> True`（cases 分解 e 取 witness 后 exact True.intro——训练"取出"方向） | 双向 |

### 5.5 Iff 世界

| 关 | 命题 | 教学点 |
|---|---|---|
| 1 | `Iff a a` | Iff.intro + exact |
| 2 | `Iff a b -> Iff b a` | 对称（mp/mpr 互换） |
| 3 | `Iff a b -> Iff b c -> Iff a c` | 传递（剧本 12 复用） |
| 4 | `(a -> b) -> (b -> a) -> Iff a b` | Iff.intro 反向 |
| 5 | `Iff a b -> Iff (Not a) (Not b)` | Iff 与 Not 组合 |

### 5.6 Combo 世界（综合）

| 关 | 命题 | 教学点 |
|---|---|---|
| 1 | `Or (And a b) (And a c) -> And a (Or b c)` | 分配律反向（剧本 14 复用） |
| 2 | `Not (Or a b) -> And (Not a) (Not b)` | De Morgan 全量版 |
| 3 | `(Or a b -> c) -> And (a -> c) (b -> c)` | 函数到合取（curry 式） |
| 4 | `And (a -> b) (a -> c) -> a -> And b c` | 合取构造 + 应用 |
| 5 | `Not (Not (Or a (Not a)))` | 排中律直觉主义版（剧本 15 复用） |

内容创作顺序：先设计 md（playbook 重写），再生成 `.game` 文件，
最后逐关 REPL 验证标准解。

## 6. playbook.md 重新定位

`tutorials/prove-playbook.md` 重写为**游戏设计文档**：

- 第 1 部分：三节路径保留为"教学法总览"（λ → recursor → 独立证明）
- 第 2 部分：每世界一章——关卡列表（命题 + 设计意图 + 标准解 + ban 理由），
  与 `worlds/*.game` 双向对照
- 新增"加关卡指南"：如何写 `.game` 文件（格式 + 验证命令
  `repl --game <世界> --check-level N` 或直接游玩验证）

## 7. opencode skill 集成（spike 结论）

### 7.1 调研结论

- **skill 为主**（不是 plugin）：nanobruijn 已有 CLI，skill 教会 AI 调用即可，
  零 JS/TS 维护；教学 REPL 无状态（每行新 TypeChecker），与 AI 的 bash 调用
  天然匹配；plugin 的价值（结构化 tool）在 `--json` 输出下收益有限
- 可选 agent：`.opencode/agents/nanobruijn-tutor.md`（bash 只放行
  `py-nanobruijn*`）用于批改工作流
- 参考先例：`~/.opencode/skills/lean4/SKILL.md`（决策表结构）

### 7.2 CLI 非交互参数（前置条件）

```
py-nanobruijn repl --script "#check forall (a : Prop), a -> a"   # 单发执行，输出纯文本
py-nanobruijn repl --json                                        # 结构化输出（与 --script 组合）
```

- `--script <文本>`：复用 `process_line`（repl.py:25），单行执行后退出
  （支持 `#check`/`#prove`+tactic 序列，以换行分隔）
- `--json`：输出 `{ok, type, error, ...}` 便于 AI 判读
- `--game <世界> --level N`：关卡验证入口（AI 检查某关可解性）
- `--timeout` 已存在（默认 5.0s），防 AI 卡死

### 7.3 交付物

```
nanobruijn/.opencode/
  skills/nanobruijn/SKILL.md      # 主入口（仿 lean4 结构：调用规则表 + 工作流 + anti-patterns）
  agents/nanobruijn-tutor.md      # 可选批改 subagent
```

`SKILL.md` 骨架：

```markdown
---
name: nanobruijn
description: "Verify Lean proofs with nanobruijn. Grade student submissions via `py-nanobruijn repl --script`. Load game levels."
---
- 调用规则表：验证 → --script #check；批改 → --script #prove + tactic 序列；
  查常量 → #print；游戏关卡 → --game
- 工作流：--script 单发 → 读输出 → 反馈循环（无状态重放）
- Anti-patterns：❌ 起交互式 repl（挂起）→ ✅ 永远 --script；
  ❌ 猜类型 → ✅ #check；⚠️ NatLit 教学 REPL 拦截等已知坑
```

### 7.4 未来升级到 plugin 的条件

结构化 tool（`nanobruijn_check(expr)`）、跨项目分发、钩子强制 `--script`
防挂起——目前不需要，YAGNI。

## 8. 测试策略

- `test_teaching.py::TestGame`（新类）：
  - 解析器：合法/非法 `.game` 文件（缺 world/goal、坏 ban 名）
  - 状态机：星级计算（1/2/3 星路径）、解锁顺序、ban 生效、存档读写
  - 集成：`#game` 进入世界 → 用标准解通关 → 星级正确；`--script --json`
    输出结构
- 每关标准解**真实 REPL 验证**（脚本测试或手动）——与 prove-playbook
  剧本同标准
- 提交前：`pytest py_nanobruijn -q` 全绿 + `ruff check py_nanobruijn`

## 9. 范围与边界

- 不改内核（`tc_*.py`/`dag.py`/`env.py`/NDJSON `parser.py`/`expr.py`）——
  `game.py`/`repl.py`/`__main__.py`/`.opencode/` 均为教学层
- 不做：玩家自创关卡 UI、多玩家、网络存档、plugin 升级（7.4 条件触发时才做）
- `#prove` 现有行为不变（游戏关卡是它的包装层）