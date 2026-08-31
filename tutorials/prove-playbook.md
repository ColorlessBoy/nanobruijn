# 🎯 教学剧本：关卡世界设计文档（#prove Playbook）

> 本文档是 GAME 模式的关卡设计文档：md 与 worlds/*.game 双向对照——
> 先在这里设计，再落成 .game 文件，最后用 REPL 验证。
> 配套工具：py-nanobruijn repl 的 #game 模式（关卡闯关）。
>
> 6 个世界 30 关，全部标准解与 `worlds/*.game` 逐字一致，由
> `TestWorldSolutions` 持续验证；本文档任何改动都必须同步 .game（反之亦然）。

---

## 怎么玩

启动 REPL 后（`py-nanobruijn repl`），游戏相关命令：

| 命令 | 作用 |
|---|---|
| `#worlds` | 列出全部世界与你的进度，如 `And — 合取世界：从构造到分解（3/5 关）` |
| `#game <世界>` | 进入世界（如 `#game And`；世界名不区分大小写，对应 `worlds/<world>.game`） |
| `hint` | 关卡内逐条显示分层提示（`提示 1/2`、`提示 2/2`……每条 hint 降一星） |
| `solution` | 显示标准解并退出本关回主 REPL（本关未通关、不计星；下次 `#game` 从同关继续） |
| `#quit` / `abort` | 中途退出当前证明 |

**进入世界后**，自动从第一个未完成关卡开始，顺序解锁（第 N 关需要第 N-1 关已
通关）。每关打印关卡名、命题与上下文，`proof>` 提示符下输入 tactic——
`intro`/`apply`/`exact`/`cases`（计入步数）、`done`（合成 + 内核检查）。每行
tactic 后观察三件事：

1. **上下文**——手头有哪些"已知为真"的东西
2. **目标**——还差什么证明
3. **当前项**——证明 lambda 长什么样了（这是最关键的：tactic 在"编辑"这个 lambda）

关卡引擎就是 `#prove` 内核：每关 goal 是一个命题，`done` 合成完整 lambda 后
过内核检查才算过关。每关有**星级**（1-3★）：

- 3★：没用 hint 且步数 ≤ 标准解步数（标准解越短，3★ 越难）
- 2★：用了 1 条 hint，或步数超限（每条 hint 降一星）
- 1★：用了 ≥2 条 hint

过关时打印你的星级和标准解（"你的路径可能不同，两种都正确"）；关卡可能带
**ban**（禁用 tactic，如 `ban: cases`），输入被禁用 tactic 会提示换一条路。

**存档**：星数持久化到 `py_nanobruijn/saves/<World>.json`（如
`saves/And.json`），重启 REPL 进度仍在；`#worlds` 显示的进度就来自存档。
世界通关时显示 `🎉 世界通关！全部关卡完成。`

---

## 学习路径（第一公里）

这是一条从零开始的完整路径，分三节，每节大约一小时：

| 节 | 主题 | 世界 | 学完后你能 |
|---|---|---|---|
| **第 1 节** | λ 与类型——认识证明的语言 | Not（前 2 关）+ Iff（前 3 关） | 读懂 `fun`/`∀`/`->`，手写简单证明 |
| **第 2 节** | recursor——遇见结构 | And + Or + Exists | 用 `cases` 分解结构 |
| **第 3 节** | 独立证明——终点 | Not/Iff 后段 + Combo | 独立完成组合证明 |

**路线图**：每节的世界按难度递增；第 2 节依赖第 1 节的 `apply`/`exact`；
第 3 节会用到前两节的所有技巧（含 `cases h as a b` 自定义名）。每节的检验
标准：对应世界全部 3★ 通关（每节末尾的"自己试试"见各世界章节的进阶练习）。

---

# 世界设计（与 worlds/*.game 对照）

> 以下六章 = 六个世界文件。每章先给关卡总表（关号/名称/命题/设计意图/ban），
> 再逐关给出 hints 设计、标准解与 ban 理由——所有 goal/hint/solution 与
> `.game` 文件逐字一致。设计意图是本文档新增的元信息（.game 无此字段）。

## And 世界（worlds/and.game，5 关）

> **intro**（.game 原文）：你面前是合取的世界。目标是以 a → b → a ∧ b 为起点的
> 所有通路：构造它（And.intro），拆开它（And.right / And.left，以及 cases）。

| 关 | 名称 | 命题 | 设计意图 | ban | 标准解见 |
|---|---|---|---|---|---|
| 1 | 初见合取 | `a -> b -> And a b` | And.intro 构造 | — | And-1 |
| 2 | 只取右半 | `And a b -> b` | 投影 And.right（禁 cases 逼投影） | cases | And-2 |
| 3 | 结合律 | `And (And a b) c -> And a (And b c)` | 嵌套 cases + 自定义名 | — | And-3 |
| 4 | 交换律 | `And a b -> And b a` | and_comm：第一个 rec 证明 | — | And-4 |
| 5 | 矛盾：不可兼得 | `Not a -> Not (And a b)` | cases + 矛盾（hna ha : False） | — | And-5 |

**教学法要点（原 #prove 剧本对应）**：本世界承载第 2 节"recursor——遇见结构"
的开场。剧本 5（合取构造）的教学点并入 And-1；剧本 7（and_comm，第一个 rec
证明——`cases` 是"自动构造 And.rec 应用"，分解规则不是魔法，就是 `And.rec`
的类型说的）并入 And-4；剧本 10（合取与否定矛盾）并入 And-5。

### And-1 初见合取

- **命题**：`forall (a : Prop), forall (b : Prop), a -> b -> And a b`
- **设计意图**：世界第一关，`apply And.intro` 从目标反推构造子；隐式参数
  `{a}{b}` 从目标自动匹配，显式参数变两个子目标（"洞"）。对应剧本 5。
- **hints 设计**（2 条）：
  1. 目标头部是 And —— 先 apply And.intro
  2. 剩下两个子目标 a 和 b：第一个 intro 引入后 exact，第二个同理
- **标准解**（7 步，3★ 上限）：

```text
intro a
intro b
intro ha
intro hb
apply And.intro
exact ha
exact hb
```

### And-2 只取右半

- **命题**：`forall (a : Prop), forall (b : Prop), And a b -> b`
- **设计意图**：合取分解有两条路——投影（`And.right`）与 `cases`。本关 **ban
  cases**，逼玩家认识投影：结论是裸变量 `b`，投影的结果也是裸变量，`apply`
  只匹配常量头部，所以用 `exact`。
- **hints 设计**（2 条）：
  1. 结论是 b，但前提是 And a b。试试投影 And.right
  2. intro 引入 h : And a b 后，用 exact And.right a b h 一步收工（And.right 是"取右半"的投影）
- **ban 理由**：禁 `cases`，否则投影路线完全被跳过——本关唯一教学点是
  "投影 = 应用"。
- **标准解**（4 步，3★ 上限）：

```text
intro a
intro b
intro h
exact And.right a b h
```

### And-3 结合律

- **命题**：`forall (a : Prop), forall (b : Prop), forall (c : Prop), And (And a b) c -> And a (And b c)`
- **设计意图**：嵌套 cases 的第一次登场——外层 `cases h as hab hc` 后，`hab`
  本身还是合取，再 `cases hab as ha hb`；每层结构对应一个 recursor。这也是
  原 15 剧本"综合自测 2"（合取结合律，双重重合取 cases）的正式关卡。
- **hints 设计**（3 条）：
  1. 前提 And (And a b) c 先 intro h 引入，再 cases h 得到 hab : And a b 与 hc : c——目标保持 And a (And b c)
  2. 目标 And a (And b c) 里的嵌套前提也需要拆：cases hab 得到 ha : a 与 hb : b（hc 仍在作用域内）
  3. 现在 apply And.intro 拆目标为 a 和 And b c：前者 exact ha，后者再 apply And.intro 用 hb / hc
- **标准解**（11 步，3★ 上限）：

```text
intro a
intro b
intro c
intro h
cases h as hab hc
cases hab as ha hb
apply And.intro
exact ha
apply And.intro
exact hb
exact hc
```

### And-4 交换律

- **命题**：`forall (a : Prop), forall (b : Prop), And a b -> And b a`
- **设计意图**：剧本 7 原题（and_comm）——第一个真正的 rec 证明。`cases x`
  把 `x : And a b` 分解成 `ha : a, hb : b`，部分项是
  `@And.rec a b (fun (_ : And a b) => And b a) x (fun ha => fun hb => _)`
  骨架。`#print and_comm` 显示的内置证明项与标准解一模一样。
- **hints 设计**（1 条，刻意稀疏——这是"自己试试"的过渡关）：
  1. 和上一关同样的模式：apply And.intro 拆目标，cases 拆前提
- **标准解**（7 步，3★ 上限）：

```text
intro a
intro b
intro h
cases h as ha hb
apply And.intro
exact hb
exact ha
```

### And-5 矛盾：不可兼得

- **命题**：`forall (a : Prop), forall (b : Prop), Not a -> Not (And a b)`
- **设计意图**：`cases` + 矛盾：`h : And a b` 分解出 `ha : a`，与前提
  `hna : Not a` 冲突，`exact hna ha`（`hna ha : False`）完成。目标
  `Not (And a b)` 是函数类型（`And a b -> False`），`intro` 展开定义即可。
  对应剧本 10 的教学点（"矛盾不可能"的最朴素证明）。
- **hints 设计**（3 条）：
  1. Not a 就是 a -> False。目标 Not (And a b) 也是函数类型：intro
  2. 引入 h : And a b 后目标是 False —— cases h 分解出 ha : a，矛盾出现
  3. 用 hna ha 得到 False，exact 收工
- **标准解**（6 步，3★ 上限）：

```text
intro a
intro b
intro hna
intro h
cases h as ha hb
exact hna ha
```

---

## Or 世界（worlds/or.game，5 关）

> **intro**（.game 原文）：析取 a ∨ b 的证明是「要么左边要么右边」：Or.inl 走左路，
> Or.inr 走右路。从前提里用 a ∨ b 时，必须两条路都铺好（Or.rec 的本质）。

| 关 | 名称 | 命题 | 设计意图 | ban | 标准解见 |
|---|---|---|---|---|---|
| 1 | 左路 | `a -> Or a b` | Or.inl 构造 | — | Or-1 |
| 2 | 右路 | `b -> Or a b` | Or.inr 构造 | — | Or-2 |
| 3 | 消去律：两条路都要走 | `Or a b -> (a -> c) -> (b -> c) -> c` | Or.rec 的本质（cases 双分支） | — | Or-3 |
| 4 | 交换律 | `Or a b -> Or b a` | 双分支 cases + 方向选择 | — | Or-4 |
| 5 | 析取消去与矛盾 | `Or a b -> Not a -> b` | @False.rec：矛盾导出任意命题 | — | Or-5 |

**教学法要点（原 #prove 剧本对应）**：剧本 8（析取交换律，`Or.rec` 的类型就是
"析取的 case 分析"——两个分支都给结论，析取就给出结论）并入 Or-3/Or-4；
剧本 9（否定析取：`Not (Or a b)` 分解后每支变矛盾）的教学点并入 Or-5（左路
`ha : a` 与 `hna` 矛盾即"否定把分支变矛盾"的镜像）。

### Or-1 左路

- **命题**：`forall (a : Prop), forall (b : Prop), a -> Or a b`
- **设计意图**：`apply Or.inl` 选择左路构造析取。
- **hints 设计**（2 条）：
  1. 目标头部是 Or —— apply Or.inl 选择左路
  2. 剩下目标 a，intro 后 exact
- **标准解**（5 步，3★ 上限）：

```text
intro a
intro b
intro ha
apply Or.inl
exact ha
```

### Or-2 右路

- **命题**：`forall (a : Prop), forall (b : Prop), b -> Or a b`
- **设计意图**：与左路对称，`apply Or.inr`。构造析取的两条路都走过之后，
  才能理解"从前提析取要两条路都铺好"（下一关）。
- **hints 设计**（2 条）：
  1. 目标头部是 Or —— apply Or.inr 选择右路
  2. 剩下目标 b，intro 后 exact
- **标准解**（5 步，3★ 上限）：

```text
intro a
intro b
intro hb
apply Or.inr
exact hb
```

### Or-3 消去律：两条路都要走

- **命题**：`forall (a : Prop), forall (b : Prop), forall (c : Prop), Or a b -> (a -> c) -> (b -> c) -> c`
- **设计意图**：析取消去的本质——前提 `Or a b` 必须两条路都走：`cases h` 分两
  路，左路 `ha : a` 用 `h1`，右路 `hb : b` 用 `h2`。这就是 `Or.rec` 的本质，
  `cases` 替你写好了骨架（`@Or.rec a b (fun _ => c) _ _ h`）。
- **hints 设计**（2 条）：
  1. 前提 Or a b 必须两条路都走：cases h 分两路
  2. 左路 ha : a 用 h1，右路 hb : b 用 h2 —— 这就是 Or.rec 的本质，cases 替你写好了
- **标准解**（9 步，3★ 上限）：

```text
intro a
intro b
intro c
intro h
intro h1
intro h2
cases h as ha hb
exact h1 ha
exact h2 hb
```

### Or-4 交换律

- **命题**：`forall (a : Prop), forall (b : Prop), Or a b -> Or b a`
- **设计意图**：剧本 8 原题（or_comm）——`cases` 双分支后，每个分支用
  `apply` 指向对应方向（左路 `ha` 进 `Or.inr`，右路 `hb` 进 `Or.inl`）。
  对应原进阶练习 1。
- **hints 设计**（1 条）：
  1. 前提 Or a b 用 cases 分两条路；每条路都用 apply 指向对应方向
- **标准解**（7 步，3★ 上限）：

```text
intro a
intro b
intro h
cases h as ha hb
apply Or.inr
exact ha
apply Or.inl
exact hb
```

### Or-5 析取消去与矛盾

- **命题**：`forall (a : Prop), forall (b : Prop), Or a b -> Not a -> b`
- **设计意图**：矛盾导出任意命题（ex falso）：左路 `ha : a` 与 `hna : Not a`
  矛盾，用 `@False.rec`（motive := `fun _ => b`）消去；右路 `hb : b` 直接
  exact。`False.rec` 是唯一能从 `False` 里拿出任意命题的手段。
- **hints 设计**（1 条）：
  1. cases h 分两路：左路 ha : a 与 hna 矛盾——@False.rec 消去（motive := fun _ => b）；右路 hb : b 直接 exact
- **标准解**（8 步，3★ 上限）：

```text
intro a
intro b
intro h
intro hna
cases h as ha hb
exact @False.rec.{0} (fun (anon : False) => b) (hna ha)
exact hb
```

---

## Not 世界（worlds/not.game，5 关）

> **intro**（.game 原文）：否定 ¬a 不是魔法，它就是 a → False：一个把 a 的证明
> 变成荒谬的函数。这一关的世界里，你会学会用这个定义思考。

| 关 | 名称 | 命题 | 设计意图 | ban | 标准解见 |
|---|---|---|---|---|---|
| 1 | 否定的定义 | `(a -> False) -> Not a` | Not 是定义不是原语 | — | Not-1 |
| 2 | 双重否定引入 | `a -> Not (Not a)` | 嵌套 Not 展开 | — | Not-2 |
| 3 | 三重否定弱化 | `Not (Not (Not a)) -> Not a` | 最内层 lambda 的形状 | — | Not-3 |
| 4 | 逆否：mt 的手写 | `(a -> b) -> Not b -> Not a` | 嵌套应用 hnb (hab hna) | — | Not-4 |
| 5 | 析取的否定：拆开它 | `Not (Or a b) -> Not a` | 否定前提 = 函数，构造论证 | cases | Not-5 |

**教学法要点（原 #prove 剧本对应）**：本世界承载第 1 节开场。剧本 1（恒等：
最朴素的证明 = 参数原样返回，lambda 的每个 binder 对应一次 `intro`）的精华
在 Not-1/Not-2 的 `exact h ha` 里；剧本 4（三重否定弱化）原题即 Not-3，其
教学点"`intro` 会先展开定义（`Not a` 变成 `a -> False`）——与真实 Lean 行为
一致；否定就是'蕴含 False'"并入 Not-1/Not-3；剧本 6（mt 的手写）原题即
Not-4。

### Not-1 否定的定义

- **命题**：`forall (a : Prop), (a -> False) -> Not a`
- **设计意图**：世界第一关，认识"`Not a` 是 `a -> False` 的缩写"。目标
  `Not a` 展开就是函数类型，`intro` 即可；前提 `h : a -> False` 直接喂
  `ha : a`。
- **hints 设计**（2 条）：
  1. 目标 Not a 展开就是 a -> False：intro 即可
  2. 把前提 h 的证明 exact 上去
- **标准解**（4 步，3★ 上限）：

```text
intro a
intro h
intro ha
exact h ha
```

### Not-2 双重否定引入

- **命题**：`forall (a : Prop), a -> Not (Not a)`
- **设计意图**：`Not (Not a)` 是 `(Not a) -> False`——两层定义展开。有了
  `ha : a` 和 `h : Not a`，`h ha : False`。注意：`Not (Not a)` 在直觉主义里
  永远成立，但 `Not (Not a) -> a` 不行（那是双否消去，经典逻辑才有）——
  Combo-5 会再次遇到这个边界。
- **hints 设计**（2 条）：
  1. 目标 Not (Not a) 展开是 (Not a) -> False：intro h
  2. 现在目标是 False，而 h : Not a 即 a -> False —— h ha 就是 False
- **标准解**（4 步，3★ 上限）：

```text
intro a
intro ha
intro h
exact h ha
```

### Not-3 三重否定弱化

- **命题**：`forall (a : Prop), Not (Not (Not a)) -> Not a`
- **设计意图**：剧本 4 原题。证明的 lambda 形状最内层
  `fun (hnn : Not a) => hnn hna` 是一个 `Not a` 的证明（收 `hnn : a -> False`，
  喂 `hna : a` 得 `False`），整体交给 `h : Not (Not (Not a))`。
- **hints 设计**（3 条）：
  1. 目标 Not a：intro hna（展开后 binder 是 a : Prop，所以 hna : a），目标 False
  2. 前提 h : Not (Not (Not a)) 需要 Not (Not a) 的证明 —— 由 a 的双重否定引入可得
  3. 构造 fun (hnn : Not a) => hnn hna：hnn hna : False ✓（hnn : a -> False）
- **标准解**（4 步，3★ 上限）：

```text
intro a
intro h
intro hna
exact h (fun (hnn : Not a) => hnn hna)
```

### Not-4 逆否：mt 的手写

- **命题**：`forall (a : Prop), forall (b : Prop), (a -> b) -> Not b -> Not a`
- **设计意图**：剧本 6 原题（mt）。`hnb (hab hna)` 的嵌套应用——先 `hab` 后
  `hnb`；`#print mt` 的内置证明项与标准解一模一样。证明"如果 a 则 b，且 b 为
  假，则 a 为假"。原剧本 3（flip：`f : a -> b -> c` 先收 `a` 再收 `b`，目标
  顺序交换则 `f xa yb`）的"参数顺序"意识在这里第一次有用——嵌套应用谁在外
  谁在内，决定证明的形状。
- **hints 设计**（2 条）：
  1. 目标 Not a：intro hna，目标 False
  2. 前提有 hab : a -> b 与 hnb : Not b —— hnb (hab hna) 就是 False
- **标准解**（5 步，3★ 上限）：

```text
intro a
intro b
intro hab
intro hnb
intro hna
exact hnb (hab hna)
```

### Not-5 析取的否定：拆开它

- **命题**：`forall (a : Prop), forall (b : Prop), Not (Or a b) -> Not a`
- **设计意图**：ban cases 的第二关（与 And-2 呼应）。`h : Not (Or a b)` 是
  函数不是结构——`cases` 无从拆起（拆它得到的是 `Or a b -> False` 的输入，
  不是分支）。正确路线：**反向构造** `Or a b` 的证明（`Or.inl a b hna`）交给
  `h`。教学点：否定前提 = 函数，用"构造论证"而不是分解。
- **hints 设计**（2 条）：
  1. 目标 Not a：intro hna，目标 False
  2. 前提 h : Not (Or a b) —— 构造 Or a b 的证明（Or.inl hna）交给 h 即可
- **ban 理由**：禁 `cases`，否则玩家会试图"拆开" `h`——本关教学点正是
  "否定前提是函数，不能拆，只能喂"。
- **标准解**（5 步，3★ 上限）：

```text
intro a
intro b
intro h
intro hna
exact h (Or.inl a b hna)
```

---

## Exists 世界（worlds/exists.game，5 关）

> **intro**（.game 原文）：存在命题 ∃x, p x 的证明是一个「证人」：x 以及 p x 的
> 证明。反向使用（从 ∃x, p x 里取证人）则是 cases 的领地。

| 关 | 名称 | 命题 | 设计意图 | ban | 标准解见 |
|---|---|---|---|---|---|
| 1 | 平凡的存在 | `@Exists.{1} Prop (fun (x : Prop) => x) -> True` | True.intro：结论平凡，前提可不用 | — | Exists-1 |
| 2 | 证人传递（Exists.imp 方向一） | `(forall x, p x -> q x) -> Exists p -> Exists q` | cases 取证人 + Exists.intro 给出 | — | Exists-2 |
| 3 | 矛盾的否定（not_exists 方向） | `(forall x, p x -> False) -> Exists p -> False` | cases 取证人 + h x hx : False | — | Exists-3 |
| 4 | 冗余的包装 | `Exists (fun x => p x) -> Exists p` | β 归约：包装解开就是 p x | — | Exists-4 |
| 5 | 取出与给出 | `Exists p -> p a -> True` | 组合练习：True.intro 收工 | — | Exists-5 |

**教学法要点（原 #prove 剧本对应）**：剧本 11（存在量词）的教学点全部并入
Exists-2：`cases` 从"存在"里取出 witness（部分项是
`@Exists.rec.{1} Prop p (fun _ => ...) (fun x => fun hx => _) e`）；
**存在量词的证明 = 给出 witness**；`.{1}` 是 universe 显式实例化
（`Prop : Sort 1`）。原"综合自测 3"（`Exists.imp` 手写版）即 Exists-2 的
前半。Exists-4 额外展示解析期 OSNF 归一化：`(fun x => p x) x` 化简就是
`p x`。

### Exists-1 平凡的存在

- **命题**：`@Exists.{1} Prop (fun (x : Prop) => x) -> True`
- **设计意图**：热身关——结论是 `True`，`exact True.intro` 一步收工，前提
  甚至不用（`True.intro` 是唯一构造子，无参数）。想练习分解也可以
  `cases h` 取出证人 `x : Prop` 与 `hx : x`。
- **hints 设计**（2 条）：
  1. 结论是 True —— 直接 exact True.intro，前提甚至可以不用
  2. 如果想练习分解：cases h 得到 x : Prop 与 hx : x，然后 exact True.intro
- **标准解**（2 步，3★ 上限）：

```text
intro h
exact True.intro
```

### Exists-2 证人传递（Exists.imp 方向一）

- **命题**：`forall (p : Prop -> Prop), forall (q : Prop -> Prop), forall (h : forall (x : Prop), p x -> q x), @Exists.{1} Prop p -> @Exists.{1} Prop q`
- **设计意图**：剧本 11 教学点全集：`cases e` 取出证人 `x` 与 `hx : p x`；
  目标 `Exists q` 用 `exact @Exists.intro.{1} Prop q x (h x hx)` 一步给出
  证人（`apply` 只支持常量，recursor/构造子带参数用 `exact`）。对应原综合
  自测 3（`Exists.imp` 手写版）。
- **hints 设计**（2 条）：
  1. 前提 e : Exists p —— cases e 取出证人 x 与 hx : p x
  2. 目标 Exists q：exact @Exists.intro.{1} Prop q x (h x hx) 一步给出证人（apply 只支持常量，recursor/构造子带参用 exact）
- **标准解**（6 步，3★ 上限）：

```text
intro p
intro q
intro h
intro e
cases e as x hx
exact @Exists.intro.{1} Prop q x (h x hx)
```

### Exists-3 矛盾的否定（not_exists 方向）

- **命题**：`forall (p : Prop -> Prop), (forall (x : Prop), p x -> False) -> @Exists.{1} Prop p -> False`
- **设计意图**：`cases` 取证人后矛盾直接落地：`h x hx : False`。与 Or-5 的
  `False.rec` 不同，这里目标是 `False` 本身，不需要消去——展示"存在 + 全称
  否定 = 矛盾"。
- **hints 设计**（2 条）：
  1. cases e 取证人 x 与 hx : p x
  2. h x hx : False —— 直接 exact
- **标准解**（5 步，3★ 上限）：

```text
intro p
intro h
intro e
cases e as x hx
exact h x hx
```

### Exists-4 冗余的包装

- **命题**：`forall (p : Prop -> Prop), @Exists.{1} Prop (fun (x : Prop) => p x) -> @Exists.{1} Prop p`
- **设计意图**：`Exists (fun x => p x)` 分解出的证明是 `(fun x => p x) x`——
  归一化后就是 `p x`。教学点：函数包装不改变内容（解析期 OSNF 归一化保证
  内核里它已经是 `p x`），witness 原样传递。
- **hints 设计**（2 条）：
  1. 左边 Exists (fun x => p x) 分解出 x 与 (fun x => p x) x —— 后者就是 p x
  2. exact @Exists.intro.{1} Prop p x hx 一步给出证人
- **标准解**（5 步，3★ 上限）：

```text
intro p
intro e
cases e as x hx
exact @Exists.intro.{1} Prop p x hx
```

### Exists-5 取出与给出

- **命题**：`forall (p : Prop -> Prop), forall (a : Prop), @Exists.{1} Prop p -> p a -> True`
- **设计意图**：组合练习收尾——前提给了证人但结论平凡，`True.intro` 直接
  收工；也可以 `cases e` 看看证人在哪再收工。教学点：**能用多简单的证明，
  就用多简单**——不需要把每个前提都用上。
- **hints 设计**（2 条）：
  1. 结论 True：直接 exact True.intro
  2. 想练习分解就 cases e 看看证人在哪
- **标准解**（5 步，3★ 上限）：

```text
intro p
intro a
intro e
intro hpa
exact True.intro
```

---

## Iff 世界（worlds/iff.game，5 关）

> **intro**（.game 原文）：等价 a ↔ b 是两座桥：Iff.mp 从 a 到 b，Iff.mpr 从 b
> 到 a。Iff.intro 则同时铺两条路。

| 关 | 名称 | 命题 | 设计意图 | ban | 标准解见 |
|---|---|---|---|---|---|
| 1 | 自反 | `Iff a a` | apply Iff.intro 双方向 + 恒等 | — | Iff-1 |
| 2 | 对称 | `Iff a b -> Iff b a` | mp/mpr 的使用方向 | — | Iff-2 |
| 3 | 传递 | `Iff a b -> Iff b c -> Iff a c` | 嵌套 mp/mpr 组合（Iff.trans） | — | Iff-3 |
| 4 | 逆方向构造 | `(a -> b) -> (b -> a) -> Iff a b` | 从两方向函数组装等价 | — | Iff-4 |
| 5 | 等价保持否定 | `Iff a b -> Iff (Not a) (Not b)` | mt 模式 × 等价两方向 | — | Iff-5 |

**教学法要点（原 #prove 剧本对应）**：本世界承载第 1 节收尾。剧本 1（恒等：
最朴素的证明 = 直接把参数原样返回）即 Iff-1 的两个方向；剧本 12（Iff.trans：
前两节所有技巧合流——`apply Iff.intro` 结构、`intro` 消解、`exact` 里的嵌套
应用；内置版用 `Function.comp`，手写是展开版，两种都正确，`def_eq` 判定定义
相等）原题即 Iff-3；剧本 2（蕴含传递 = `Function.comp` 的 lambda 手写版，
`#print Function.comp` 对比）的教学点并入 Iff-3。

### Iff-1 自反

- **命题**：`forall (a : Prop), Iff a a`
- **设计意图**：`apply Iff.intro` 产生两个子目标，都是 `a -> a`——每个方向
  都是剧本 1 的恒等证明（`intro ha` / `exact ha`）。注意两处 `intro ha` 在
  不同作用域，名字可以重复使用。
- **hints 设计**（1 条）：
  1. apply Iff.intro 后两个目标都是 a -> a
- **标准解**（6 步，3★ 上限）：

```text
intro a
apply Iff.intro
intro ha
exact ha
intro ha
exact ha
```

### Iff-2 对称

- **命题**：`forall (a : Prop), forall (b : Prop), Iff a b -> Iff b a`
- **设计意图**：认识两座桥的方向：`Iff.mp` 正向（a → b），`Iff.mpr` 反向
  （b → a）。目标 `Iff b a` 的第一个方向 `b -> a` 用 `mpr`，第二个方向
  `a -> b` 用 `mp`——方向和桥的配对是本关的难点。
- **hints 设计**（3 条）：
  1. 前提 Iff a b 先 intro h 引入，再 apply Iff.intro 拆两个方向
  2. 第一个方向 b -> a：intro hb 后 exact Iff.mpr a b h hb
  3. 第二个方向 a -> b：intro ha 后 exact Iff.mp a b h ha
- **标准解**（8 步，3★ 上限）：

```text
intro a
intro b
intro h
apply Iff.intro
intro hb
exact Iff.mpr a b h hb
intro ha
exact Iff.mp a b h ha
```

### Iff-3 传递

- **命题**：`forall (a : Prop), forall (b : Prop), forall (c : Prop), Iff a b -> Iff b c -> Iff a c`
- **设计意图**：剧本 12 原题（Iff.trans）——第 1 节技巧合流：`apply Iff.intro`
  （结构）、`intro`（消解）、`exact` 里的嵌套应用
  （`Iff.mp b c hbc (Iff.mp a b hab ha)`）。`#print Iff.trans` 对比：内置版用
  `Function.comp`，标准解是展开版——`def_eq` 判定定义相等。蕴含传递
  （剧本 2，`Function.comp` 手写版）就是这个嵌套应用的纯函数版本。
- **hints 设计**（3 条）：
  1. 两个前提先 intro hab hbc 引入，再 apply Iff.intro 拆两方向，各用 mp/mpr 组合
  2. a -> c：Iff.mp b c hbc (Iff.mp a b hab ha)
  3. c -> a：Iff.mpr a b hab (Iff.mpr b c hbc hc)
- **标准解**（10 步，3★ 上限）：

```text
intro a
intro b
intro c
intro hab
intro hbc
apply Iff.intro
intro ha
exact Iff.mp b c hbc (Iff.mp a b hab ha)
intro hc
exact Iff.mpr a b hab (Iff.mpr b c hbc hc)
```

### Iff-4 逆方向构造

- **命题**：`forall (a : Prop), forall (b : Prop), (a -> b) -> (b -> a) -> Iff a b`
- **设计意图**：与 2/3 反向——手里有两方向函数，`apply Iff.intro` 后第一个
  子目标直接 `exact h1`，第二个 `exact h2`。教学点：等价是可以**组装**的，
  `Iff.intro` 就是组装器。
- **hints 设计**（1 条）：
  1. apply Iff.intro 后第一个方向直接 exact h1，第二个 exact h2
- **标准解**（6 步，3★ 上限）：

```text
intro a
intro b
intro h1
intro h2
apply Iff.intro
exact h1
exact h2
```

### Iff-5 等价保持否定

- **命题**：`forall (a : Prop), forall (b : Prop), Iff a b -> Iff (Not a) (Not b)`
- **设计意图**：mt 模式（Not-4）在等价下的变体：每个方向都是逆否——方向一
  `Not a -> Not b`：`intro hna` 再 `intro hb`，矛盾 `hna (Iff.mpr a b h hb)`；
  方向二镜像。第 1 节终点关：λ、否定、等价三样东西合体。
- **hints 设计**（2 条）：
  1. 前提 Iff a b 先 intro h 引入，再 apply Iff.intro 拆两方向，每个方向都是逆否（mt 的模式）
  2. Not a -> Not b：intro hna，再 intro hb，矛盾 hna (Iff.mpr a b h hb)
- **标准解**（9 步，3★ 上限）：

```text
intro a
intro b
intro h
apply Iff.intro
intro hna
intro hb
exact hna (Iff.mpr a b h hb)
intro hnb
intro ha
exact hnb (Iff.mp a b h ha)
```

### 第 1 节小结：tactic 与 lambda 的对应关系

| tactic | lambda 结构 |
|---|---|
| `intro x` | `fun (x : A) => _` |
| `apply f` | `@f ... _ ?n` |
| `cases h` | `@And.rec a b (fun _ => ?goal) _ h`（rec 骨架） |
| `exact e` | `e` |
| `done` | 合成 + 内核检查 |

**记住**：`done` 之后显示的完整 lambda 项，就是证明本身。tactic 只是写它的
工具——用 `#print` 查看任何内置定理，你会看到同样的 lambda 语言。

---

## Combo 世界（worlds/combo.game，5 关）

> **intro**（.game 原文）：前五个世界的技巧在这里汇合。每一关都是一道完整的
> 谜题。提示会越来越稀疏——是时候自己铺路了。

| 关 | 名称 | 命题 | 设计意图 | ban | 标准解见 |
|---|---|---|---|---|---|
| 1 | 分配律反向 | `Or (And a b) (And a c) -> And a (Or b c)` | 双重 cases：结构递归 | — | Combo-1 |
| 2 | De Morgan 全量版 | `Iff (Not (Or a b)) (And (Not a) (Not b))` | 双向证明：构造 + 分解 | — | Combo-2 |
| 3 | 函数与合取 | `(Or a b -> c) -> And (a -> c) (b -> c)` | 前提是函数就喂构造的析取 | — | Combo-3 |
| 4 | 合取的构造与应用 | `And (a -> b) (a -> c) -> a -> And b c` | 合取里的函数拿出来应用 | — | Combo-4 |
| 5 | 排中律的直觉主义版 | `Not (Not (Or a (Not a)))` | 直觉主义 vs 经典第一课 | — | Combo-5 |

**教学法要点（原 #prove 剧本对应）**：剧本 14（分配律：先拆外层合取再拆内层
析取——**双重 cases**，每层结构都对应一个 recursor，这是"结构递归"的直观
体验）的教学点并入 Combo-1；剧本 13（析取结合律：**嵌套 cases 时必须用
`cases x as x1 x2` 自定义名**，同名 h1/h2 会冲突，名字解析找最近的那个）的
"自定义名"教训已在 And-3/Combo-1 的 `as` 用法中实践；剧本 15（排中律的直觉
主义版本：经典排中律证不出来，但双重否定可以）原题即 Combo-5；原综合自测 1
（De Morgan 全量版）即 Combo-2。原进阶练习 5（`Or (And a b) (Not b)`——直觉
主义里**不成立**的命题）提醒：卡关可能不是你的问题，而是命题真证不出来——
"证不出来"也是学习。

### Combo-1 分配律反向

- **命题**：`forall (a : Prop), forall (b : Prop), forall (c : Prop), Or (And a b) (And a c) -> And a (Or b c)`
- **设计意图**：剧本 14 的分配律（`a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c)`）反向
  半边。**双重 cases**：前提是析取，`cases h` 分两路（`h1 : And a b` /
  `h2 : And a c`），每路内用 `And.left`/`And.right` 投影取部件，`Or.inl`/
  `Or.inr` 指向对应分支。每层结构一个 recursor——结构递归的直观体验。
- **hints 设计**（3 条）：
  1. 前提是析取：cases 分两路（h1 : And a b / h2 : And a c）
  2. 左路：apply And.intro 拆目标为 a 和 Or b c——前者 exact (@And.left a b h1)，后者 apply Or.inl 再 exact (@And.right a b h1)
  3. 右路同理：h2 给出的是 c，所以 apply Or.inr 再 exact (@And.right a c h2)
- **标准解**（14 步，3★ 上限）：

```text
intro a
intro b
intro c
intro h
cases h as h1 h2
apply And.intro
exact (@And.left a b h1)
apply Or.inl
exact (@And.right a b h1)
apply And.intro
exact (@And.left a c h2)
apply Or.inr
exact (@And.right a c h2)
```

### Combo-2 De Morgan 全量版

- **命题**：`forall (a : Prop), forall (b : Prop), Iff (Not (Or a b)) (And (Not a) (Not b))`
- **设计意图**：原综合自测 1（De Morgan 全量版）。双向证明：方向一构造
  （`h (Or.inl a b ha)` / `h (Or.inr a b hb)`），方向二分解（`cases x` 分两路
  + `And.left`/`And.right` 投影）。构造与分解在同一命题的两面相遇。
- **hints 设计**（3 条）：
  1. Iff.intro 拆两方向
  2. 方向一：intro h 后 apply And.intro，两个目标各用 h (Or.inl ...) / h (Or.inr ...)
  3. 方向二：intro h 后 intro x，cases x 分两路，各用 And.left/And.right 投影
- **标准解**（15 步，3★ 上限）：

```text
intro a
intro b
apply Iff.intro
intro h
apply And.intro
intro ha
exact h (Or.inl a b ha)
intro hb
exact h (Or.inr a b hb)
intro h
intro x
cases x as x1 x2
exact (@And.left (Not a) (Not b) h) x1
exact (@And.right (Not a) (Not b) h) x2
```

### Combo-3 函数与合取

- **命题**：`forall (a : Prop), forall (b : Prop), forall (c : Prop), (Or a b -> c) -> And (a -> c) (b -> c)`
- **设计意图**：前提是函数就**喂给它构造的析取证明**：`exact h (Or.inl a b ha)`
  与 `exact h (Or.inr a b hb)`。Not-5 的"构造论证"在这里升级为对函数前提的
  通用手法。
- **hints 设计**（3 条）：
  1. 前提 (Or a b -> c) 先 intro h 引入，再 apply And.intro 拆两目标
  2. 第一个 a -> c：intro ha 后 exact h (Or.inl a b ha)
  3. 第二个 b -> c：intro hb 后 exact h (Or.inr a b hb)
- **标准解**（9 步，3★ 上限）：

```text
intro a
intro b
intro c
intro h
apply And.intro
intro ha
exact h (Or.inl a b ha)
intro hb
exact h (Or.inr a b hb)
```

### Combo-4 合取的构造与应用

- **命题**：`forall (a : Prop), forall (b : Prop), forall (c : Prop), And (a -> b) (a -> c) -> a -> And b c`
- **设计意图**：与 Combo-3 对称——合取里的函数**拿出来应用**：
  `(@And.left (a -> b) (a -> c) h1) h3`。投影 + 应用一步到位。
- **hints 设计**（2 条）：
  1. intro h1、intro h3 —— 前提 h1 : And (a -> b) (a -> c)，h3 : a
  2. apply And.intro 后两个目标：And.left h1 h3 与 And.right h1 h3
- **标准解**（8 步，3★ 上限）：

```text
intro a
intro b
intro c
intro h1
intro h3
apply And.intro
exact (@And.left (a -> b) (a -> c) h1) h3
exact (@And.right (a -> b) (a -> c) h1) h3
```

### Combo-5 排中律的直觉主义版

- **命题**：`forall (a : Prop), Not (Not (Or a (Not a)))`
- **设计意图**：剧本 15 原题（not_not_em），第一公里终点。经典排中律
  `a ∨ ¬a` 在直觉主义里**证不出来**——但它的双重否定 `¬¬(a ∨ ¬a)` **可以**！
  关键：`h : (a ∨ ¬a) -> False`，用 `Or.inr` 构造 `a ∨ ¬a`（需要 `¬a` 的
  证明）——`¬a` 就是 `a -> False`，用 `Function.comp` 把 `h` 和 `Or.inl`
  组合出来。`#print not_not_em` 对比，一模一样。
- **hints 设计**（3 条）：
  1. 经典排中律 a ∨ ¬a 直觉主义证不出来——但双重否定可以
  2. intro h 后目标 False。h 需要 Or a (Not a) 的证明：Or.inr 构造右路，其参数是 Not a
  3. Not a 就是 a -> False：用 Function.comp 把 h 和 Or.inl 组合（见 not_not_em）
- **标准解**（3 步，3★ 上限）：

```text
intro a
intro h
exact h (Or.inr a (Not a) (@Function.comp.{0, 0, 0} a (Or a (Not a)) False h (@Or.inl a (Not a))))
```

---

## 加关卡指南

新增一关的标准流程（先设计 → 落 .game → 自动验证 → 手动通关）：

1. **在本文档设计**：在对应世界章节写关卡小节——goal（教学语法写的命题）、
   设计意图、分层 hints（2-3 条，逐条递进）、ban（可选，必须是内核已知
   tactic：intro/apply/exact/cases/done/abort/context/help）、标准解草稿。
   标准解草稿先在 REPL 的 `#prove` 模式跑通（`py-nanobruijn repl` →
   `#prove <goal>`），确认它能过内核检查再抄进来。
2. **落成 .game**：追加到 `py_nanobruijn/worlds/<world>.game`。格式见
   `py_nanobruijn/teaching/game.py` 模块文档字符串（仿 core.fol 逐行风格，
   零依赖）：`world`/`title`/`intro` 头；每关 `level N`、`name`、`goal:`、
   `hint:`（可多条）、`ban:`（可多条）、`solution:`（脚本行，到 `---` /
   下一个 `level` / 文件尾为止）。关卡间用 `---` 分隔；`#` 开头是注释。
   注意 `goal:` 后直接跟命题（冒号后一个空格），`solution:` 后换行写脚本。
3. **跑自动验证**：
   ```bash
   .venv/bin/python -m pytest py_nanobruijn/test_teaching.py::TestWorldSolutions -q
   ```
   全绿才说明标准解与 .game 一致（每个世界的标准解逐行 replay 过内核）。
4. **手动通关体验**：`py-nanobruijn repl` → `#game <世界>` 从新关开始闯，
   确认：hints 顺序合理、不用 hint 也能推出来、标准解步数足够短（3★ 要求
   步数 ≤ 标准解步数——标准解太长会让 3★ 太难，太短则 3★ 太容易）。
5. **同步本文档**：更新世界章节的关卡总表与小节，保持 md ↔ .game 双向一致
   （改动 .game 必须同步 md，反之亦然）；用
   `rg -c "^name " py_nanobruijn/worlds/*.game` 核对关卡数与文档表格对照。

**检查清单**：goal 能被解析（教学语法）；标准解逐行可行且过内核；ban 的
tactic 存在；hints 不用 `solution` 就够通关；文档与 .game 关卡数、名称、
goal、标准解逐字一致。