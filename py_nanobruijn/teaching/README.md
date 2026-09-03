# py-nanobruijn 教学 REPL 使用手册

> 面向完全初学者。你不需要任何类型论或 Lean 背景，照着做就能开始玩。
> 本工具的核心承诺：**你看到的每一个行为，都来自真实 Lean 内核**——不是模拟器。

---

## 0. 这是什么东西？（30 秒版）

Lean 是一种"证明即编程"的语言：**写一个程序（lambda 表达式），证明一个命题**。
本 REPL 是一个交互式实验室，让你：

- 输入表达式，看它的**类型**（`#check`）
- 让表达式一步步**归约**（`#reduce`）
- 查询内置常量的**定义**（`#print`）
- 用**tactic 草稿模式**（`#prove`）像搭积木一样构造证明

它内置了一个"最小 Lean 内核"：逻辑连接词（And/Or/Iff/Eq…）、递归器、以及 14 个
从真实证明库移植的定理。39 个常量，启动即用，不需要下载任何东西。

---

## 1. 安装与启动

```bash
# 项目根目录（已经配置好 uv 虚拟环境）
.venv/bin/python -m py_nanobruijn repl
```

看到类似这样的界面就成功了：

```
py-nanobruijn teaching REPL
输入表达式查看类型（等价 #check），或使用命令：#check/#reduce/#print/#prove/#env/#help/#quit
语法：fun (x : A) => e、∀ (x : A), e、A -> B、@Const、Type、Prop
已加载 39 个常量，输入 #help 查看帮助
>
```

`>` 是你的提示符。输入内容，回车执行。退出：`#quit` 或 `Ctrl-D`。

---

## 2. 概念速成（5 分钟，够用了）

### 类型与命题

在 Lean 里，**命题就是类型**。下面这些"类型"同时也是命题：

| 符号 | 含义 |
|---|---|
| `Prop` | 命题的宇宙（所有命题的类型） |
| `True` / `False` | 恒真 / 恒假命题 |
| `a -> b` | "如果 a 那么 b"（蕴含） |
| `And a b` / `Or a b` | "a 且 b" / "a 或 b" |
| `Iff a b` | "a 当且仅当 b" |
| `Eq α a b` | "a 和 b 相等"（类型 α 中） |

试试：

```
> #check True
True : Prop          ← True 是 Prop（一个命题）
> #check And
And : ∀ (a : Prop), ∀ (b : Prop), Prop
```

### 证明就是"类型为命题的值"

命题 `p` 的**证明**，就是**一个类型为 `p` 的表达式**。就像 `42 : Nat` 是自然数，
`真命题的证明` 是这个命题的"居民"。逻辑上的"证明"没有魔法——就是构建一个
满足类型的 lambda 表达式。

例如 `True.intro` 是命题 `True` 的证明（Axiom 直接给出）：

```
> #check True.intro
True.intro : True
```

### 为什么是 lambda？

`a -> b` 的证明是"把 a 的证明变成 b 的证明的函数"——`fun (ha : a) => ...`。
所以证明构造 = 写 lambda 项。tactic 草稿模式（`#prove`）就是帮你**分步写这个
lambda** 的工具（见第 5 节）。

---

## 3. 第一次会话（10 分钟，手把手）

```
> #env
```
看看有哪些内置常量。你会看到 And、Or、Iff、Eq、True、False、propext、
id、Function.comp、flip，还有一批定理（and_comm、Eq.symm…）。

```
> #print And.intro
```
打印构造子的类型：
```
And.intro : ∀ {a : Prop}, ∀ {b : Prop}, ∀ (ha : a), ∀ (hb : b), And a b
  (axiom)
```
读法：给定命题 `a`、`b`，给定 `a` 的证明 `ha`、`b` 的证明 `hb`，得到 `And a b`
的证明。花括号 `{a : Prop}` 是**隐式参数**——通常不用手动填（`@` 语法可显式填）。

```
> #check @And True True
And True True : Prop
```
`@And` 表示显式传所有参数：`And` 应用到 `True` 和 `True`，结果是命题
`And True True`（"True 且 True"），它是个 Prop。

```
> #check @And.intro True True True.intro True.intro
@And.intro True True True.intro True.intro : And True True
```
**这是 `And True True` 的证明**！`{a} := True`、`{b} := True`（隐式参数填好），
`True.intro` 是 `True` 的证明，喂给 `And.intro`，得到一个类型为 `And True True`
的表达式——证明完成。

```
> #reduce (fun (x : Prop) => x) True.intro
(fun (x : Prop) => x) True.intro => True.intro  [beta]
```
β 归约：`(fun (x : Prop) => x) a` 把 `a` 代进 `x`，得到 `a`。

恭喜，你已经完成一次完整的"证明"。接下来看第 5 节的 tactic 草稿模式——那是为
更长证明准备的。

---

## 4. 命令参考

### `#check <e>`（直接输入表达式等价）

显示表达式的类型：

```
> True
True : Prop
> Prop
Prop : Type
> Type
Type : Type 1
> fun (x : Prop) => x
fun (x : Prop) => x : ∀ (x : Prop), Prop
```

### `#reduce <e>`

逐步 β/δ 归约。`[beta]` = λ 应用；`[delta]` = 定义展开：

```
> #reduce id.{0} True True.intro
@id True True.intro => (fun {α : Prop} => fun (a : α) => a) True True.intro  [delta]
(fun {α : Prop} => fun (a : α) => a) True True.intro => True.intro  [beta]
```
第一步 `[delta]`：把 `id` 的定义展开；第二步 `[beta]`：应用两个 λ。

### `#print <name>`

显示常量类型 + 定义（Axiom 标 `(axiom)`）：

```
> #print and_comm
and_comm : ∀ {a : Prop}, ∀ {b : Prop}, Iff And a b And b a
  = fun {a : Prop} => fun {b : Prop} => @Iff.intro And a b And b a ...
```

### `#env` / `#help` / `#quit`

常量列表 / 帮助 / 退出。

### `#prove <类型>`

进入**tactic 草稿模式**（下节详解）。

---

## 5. Tactic 草稿模式（`#prove`）——最重要的一节

### 先说清楚一个关键认知

**tactic 不是类型论的一部分。** 类型论只有一件事：构建 lambda 表达式。
tactic 是**编辑器**——帮你分步写出那个（往往很长、不可能一次写完的）lambda 项。
在 Lean 里 `#print` 任何定理都能看到它背后的 lambda 项——那才是"真相"；
tactic 只是写它的工具。本工具的草稿模式把这个过程**完全透明化**：

**每一步 tactic，都显示当前部分 lambda 项变成了什么样。**

### 一个完整的例子

```
> #prove ∀ (a : Prop), ∀ (b : Prop), ∀ (ha : a), ∀ (hb : b), And a b
证明: ∀ (a : Prop), ∀ (b : Prop), ∀ (ha : a), ∀ (hb : b), And a b
上下文: （空）
目标: ∀ (a : Prop), ∀ (b : Prop), ∀ (ha : a), ∀ (hb : b), And a b
当前项: _
proof> intro a
上下文: a : Prop
目标: ∀ (b : Prop), ∀ (ha : a), ∀ (hb : b), And a b
当前项: fun (a : Prop) => _
```

`intro a` = 开始写 `fun (a : Prop) => ...`。目标变小，部分项变大——**一一对应**。

继续：

```
proof> intro b
proof> intro ha
proof> intro hb
上下文: a : Prop, b : Prop, ha : a, hb : b
目标: And a b
当前项: fun (a : Prop) => fun (b : Prop) => fun (ha : a) => fun (hb : b) => _
proof> apply And.intro
目标: a
当前项: fun ... => @And.intro a b _ ?2
```

`apply And.intro` 说："我想用 `And.intro` 来构造 `And a b`"。
`And.intro` 的隐式参数 `{a}{b}` 被**自动匹配**（目标 `And a b` 告诉我们 a、b 是谁）；
剩下的显式参数（`ha : a`、`hb : b`）变成两个新目标（`_` 和 `?2`）。

```
proof> exact ha
proof> exact hb
proof> done
完整证明项:
fun (a : Prop) => fun (b : Prop) => fun (ha : a) => fun (hb : b) => @And.intro a b ha hb
内核检查: 通过
```

`exact ha` = 当前目标正好是 `ha`（`ha : a`），直接填上。
`done` = 所有洞填完 → 合成完整 lambda 项 → **真实内核检查** → 显示最终证明项。

**注意最后那行 lambda**：`fun {a} {b} => fun (ha : a) => fun (hb : b) => @And.intro a b ha hb`
——这就是你"证明"的实体。tactic 只是分步写出它的工具。用 `#print` 查看内置
定理（如 `and_comm`）会看到同样风格的项——**tactic 和手写 lambda 是同一回事**。

### tactic 清单

| tactic | 作用 | 部分项变化 |
|---|---|---|
| `intro x` | 目标 `∀ (x : A), B` → 把 `x` 加入上下文，目标变 `B` | `_` → `fun (x : A) => _` |
| `apply f` | 用常量 `f` 构造目标；隐式参数自动匹配，显式参数变新目标 | `_` → `@f ... _ ?n` |
| `exact e` | 当前目标直接用表达式 `e` 填（内核检查类型） | `_` → `e` |
| `done` | 全部填完 → 合成 + 内核检查 + 显示完整项 | — |
| `abort` | 放弃，回到主 REPL | — |
| `context` | 重新显示上下文/目标/当前项 | — |
| `help` | tactic 帮助 | — |

### 教学要点（给老师）

- **洞是编辑器的状态，不是内核的概念**——本工具没有 metavariable，洞完全由
  教学层维护，`done` 时才合成闭项交给内核。这恰好演示了"tactic 是编辑器，
  内核是裁判"的分工。
- 建议演示顺序：`#prove` 一个简单目标 → `done` 后把输出和 `#print` 内置定理的
  项对比 → 说明"我们手写的和内核里存的是同一种东西"。

---

## 6. 闯关模式（`#game` / `#worlds`）——把证明玩成游戏

在 `#prove` 的基础上，本工具内置了 **8 个闯关世界**（And/Or/Not/Exists/Iff/Combo/Hard/Eq，
各 5 关）。每一关就是一条待证明的命题，目标是**用最少步骤、不看提示**通关。

### 启动与导航

```
> #worlds
And — 合取世界：从构造到分解（0/5 关）
Or — 析取世界：选择的两条路（0/5 关）
...
> #game And
合取世界：从构造到分解
你面前是合取的世界。目标是以 a → b → a ∧ b 为起点的所有通路：构造它（And.intro），拆开它（And.right / And.left，以及 cases）。
```

或启动时直接进入：`python -m py_nanobruijn repl --game And`
（`--game` 隐含 `--fresh`：从**空环境**开始，进入世界时现场定义该逻辑词——
你会看到它的 fol 声明逐行展示并被真实加载，这就是"定义仪式"。`#check And`
在进 And 世界前会提示"它还没被定义！"。默认（无 `--fresh`）则是全量环境，
仪式只展示声明。

### 关卡内命令

进入关卡后提示符变成 `proof>`，tactic 与 `#prove` 完全相同，另有：

| 命令 | 作用 |
|---|---|
| `hint` | 逐条显示关卡提示（每条 hint 降一星） |
| `solution` | 显示标准解并放弃本关回主 REPL（不记录星级，下次从同关继续） |
| `abort` | 放弃本关回主 REPL（不记录星级） |
| `#quit` | 放弃本关，退出 REPL |

部分关卡有 `ban:` 字段（如 And 世界 L2 禁用 `cases`）——被禁用的 tactic 会直接
拒绝并提示换路（提示会指向本关设计的那条路线）。

### 亲手定义：#def 命令

想自己创造连接符？`#def` 直接把 fol 声明写进环境：

```
> #def axiom Nand : forall (a : Prop), forall (b : Prop), Prop
✚ 公理已加入环境：Nand
现在可以 #check 它、在 #prove 里使用它。
> #check Nand
Nand : ∀ (a : Prop), ∀ (b : Prop), Prop
```

- `axiom`（公设）/`def`（定义，带 `:= 值`）/`theorem`（定理，内核会检查值）
- ** axiom 是公设，内核不阻止不一致**——试试 `#def axiom Boom : False`，
  你就获得了"证明一切"的能力（这正是为什么数学里 axiom 要谨慎）
- 定义失败会带教学提示；重复定义被拒绝

### 星级与存档

- **3★**：没用 hint 且步数 ≤ 标准解行数 + 2（容错两步入 3★）；**2★**：用了 1 条 hint 或步数超限；**1★**：用了 ≥2 条 hint
- 步数只计 `intro`/`apply`/`exact`/`cases`（`context`/`help` 等不计）
- 通关后显示标准解（你的路径可能不同，两种都正确）
- 每关至少拿 1★ 才算通关；进度自动存入 `py_nanobruijn/saves/<世界>.json`
  （`#worlds` 显示各世界完成度，重新进入时自动续关）

### 世界速览

| 世界 | 主题 | 用到的新武器 |
|---|---|---|
| `And` | 合取：构造与分解 | And.intro / And.left / And.right / cases |
| `Or` | 析取：分情况讨论 | Or.inl / Or.inr / Or.rec（cases） |
| `Not` | 否定与矛盾 | Not（即 `-> False`）/ False.rec / mt |
| `Exists` | 存在量词 | Exists.intro / Exists.rec（cases） |
| `Iff` | 当且仅当 | Iff.intro / Iff.mp / Iff.mpr |
| `Combo` | 综合：多概念混合证明 | 各世界武器混用（And/Or/Not/Iff） |
| `Hard` | 挑战：第二公里（分配律/curry/映射） | 综合运用 + 投影 And.left/And.right |
| `Eq` | 等式：第三公里 | **rewrite** / @Eq.refl / 传递对称 |

---

## 7. 表达式语法

| 语法 | 含义 | 示例 |
|---|---|---|
| `fun (x : A) => e` | λ 抽象（**必须带类型注解**） | `fun (x : Prop) => x` |
| `fun {x : A} => e` | 隐式参数 λ | `fun {x : Prop} => x` |
| `∀ (x : A), e`（或 `forall`） | 依赖积（"对所有 x : A，e"） | `forall (a : Prop), a -> a` |
| `A -> B`（或 `→`） | 蕴含（匿名 binder） | `Prop -> Prop` |
| `e1 e2` | 应用（空格） | `And.intro True True True.intro True.intro` |
| `@Const a b` | 显式填隐式参数 | `@And True True` |
| `Name.{u}` | universe 实例化 | `id.{u}`、`id.{0}` |
| `Prop` / `Type` / `Sort u` | 宇宙 | `Type`、`Type u`、`Sort 0` |
| `42` | Nat 字面量 | 可解析/归约（类型推断暂不支持） |

**三条重要规则**：

1. **binder 必须带类型注解**：`fun x => e` 会报错。内核的 Lambda 需要 binder
   类型，本工具不做类型推断（这是特性：逼你明确写出每一步）。
2. **隐式参数不自动填充**（`#prove` 的 `apply` 除外）：`@And True True` 显式传。
3. **universe 参数默认实例化为 0**（Prop 层）：`id` 等价 `id.{0}`；`id.{u}` 显式
   观察 universe 多态（`∀ {α : Type u}, ∀ (a : α), α`）。

---

## 8. 内置内容（64 个常量）

### 逻辑原语（Axiom，不可 δ 展开）

| 常量 | 类型（简化写法） |
|---|---|
| `True` / `True.intro` | `Prop` / `True` |
| `False` | `Prop` |
| `And` / `And.intro` / `And.left` / `And.right` | `Prop -> Prop -> Prop` / 构造子 / 两个投影 |
| `And.rec` | `And` 的递归器（归纳） |
| `Or` / `Or.inl` / `Or.inr` / `Or.rec` | 析取 / 两个构造子 / 递归器 |
| `Iff` / `Iff.intro` / `Iff.mp` / `Iff.mpr` | 当且仅当 / 构造子 / 两个消除子 |
| `Eq` / `Eq.refl` / `Eq.rec` | 相等（universe 多态）/ 自反 / 递归器 |
| `propext` | 命题外延性：`Iff a b -> Eq Prop a b` |

### 定义（Definition，可 δ 展开）

| 常量 | 类型 | 定义 |
|---|---|---|
| `Not` | `Prop -> Prop` | `fun a => a -> False` |
| `id` | `{α : Type u} -> α -> α` | `fun {α} (a : α) => a` |
| `Function.comp` | `(β -> δ) -> (α -> β) -> α -> δ` | `fun f g x => f (g x)` |
| `flip` | `(α -> β -> φ) -> β -> α -> φ` | `fun f b a => f a b` |
| `absurd` | `a -> Not a -> b`（从矛盾推出一切） | 用 `False.rec` |

### 定理库（从 query_const.lean 移植）

| 定理 | 类型（简化） | 教学点 |
|---|---|---|
| `iff_of_true` | `a -> b -> Iff a b` | 纯构造，无递归器 |
| `Iff.refl` | `(a : Prop) -> Iff a a` | 自反 |
| `mt` | `(a -> b) -> Not b -> Not a` | 逆否（纯 lambda） |
| `not_and_of_not_left` | `Not a -> Not (And a b)` | mt + 投影 |
| `not_not_em` | `Not (Not (Or a (Not a)))` | 排中律的直觉主义版本 |
| `and_self` | `Eq Prop (And p p) p` | propext 用法 |
| `or_self` | `Eq Prop (Or p p) p` | Or.rec 用法 |
| `and_not_self` | `Not (And a (Not a))` | And.rec + absurd |
| `and_comm` | `Iff (And a b) (And b a)` | 交换律（经典练习） |
| `or_comm` | `Iff (Or a b) (Or b a)` | Or.rec 双方向 |
| `Eq.symm` | `Eq α a b -> Eq α b a` | Eq.rec 用法 |
| `Eq.trans` | `Eq α a b -> Eq α b c -> Eq α a c` | 传递性 |
| `imp.swap` | `Iff (a -> b -> c) (b -> a -> c)` | flip |
| `congrArg` | `f a = f b`（来自 `a = b`） | 等式两边套同一个函数（Eq.rec 应用） |

`#print` 任何一个定理都能看到完整证明项——建议和 `#prove` 输出的项对比阅读。

### Nat：第一个"会算"的归纳类型（nat 片段）

| 常量 | 说明 |
|---|---|
| `Nat` / `zero` / `succ` | 真归纳类型（内核 `check_inductive_declaration` 全流程检查） |
| `Nat.rec` | 递归器，规则由装载器综合——**会被 iota 归约真正执行** |
| `one` / `two` / `three` / `four` | succ 链定义（`#reduce` 可展开） |
| `add` | 在第一个参数上递归的加法 |

**为什么 Or.rec 不用算，而 Nat.rec 必须算？**

之前的连接符（Or.rec 等）都是 axiom——只是"规则的名字"。命题逻辑里一切
都是 Prop，`done` 的内核检查靠**证明无关性**（同命题的证明自动相等）短路，
从头到尾不需要"执行"任何东西。

Nat 的意义就在于计算。`#reduce add two two` 要真的得出 `four`，内核必须
执行"看 major 前提是哪个构造子 → 选对应规则 → 代入"这一步——这就是
**iota 归约**。没有它，`Nat.rec` 永远卡住，2+2 只是"一个表达式"。

试着跑：

```
#reduce add two two
#reduce add zero m
```

注意标着 `[iota]` 的步——那就是内核在执行消除规则。然后去 Nat 世界
（`#game Nat`）把 2+2=4 和第一个归纳证明亲自打出来。

（inductive 块的 fol 语法限制：无参数、无索引、Type 排序——参数化/Prop
排序归纳需要 elim-level 检查，暂不支持。）

---

## 9. 常见问题（FAQ）

| 现象 | 原因与建议 |
|---|---|
| `fun x => e` 报错 | binder 必须带类型：`fun (x : A) => e` |
| 隐式参数没自动补 | 内核无推断，用 `@` 显式；`#prove` 里 `apply` 会自动匹配 |
| `#check 42` 报 Nat 不支持 | Nat 字面量类型推断需要 Nat inductive（未内置），`#reduce 42` 可用 |
| `id` 显示 `∀ {α : Prop}` | universe 默认 0；`id.{u}` 看多态 |
| `id.{u} True` 类型错误 | Sort u ≠ Prop——内核不做 universe 推断，这正是显式 universe 的语义 |
| `#prove` 里 `apply And.rec` 报头部不匹配 | 递归器结果头是 `motive t`（变量），模式匹配只支持常量头；v1 限制 |

| 想用 recursor 做归纳 | v1 的 `apply` 不支持；可手写 `@And.rec ...`（见 `#print and_comm` 的证明项） |

---

## 10. 术语表

| 术语 | 含义 |
|---|---|
| **类型** | 表达式的分类；命题也是类型 |
| **命题** | `Prop` 的居民，如 `True`、`And a b` |
| **证明** | 类型为某命题的表达式 |
| **隐式参数** | 花括号 `{a : Prop}`，通常省略（`@` 显式填） |
| **β 归约** | `(fun x => e) a` → 代入 |
| **δ 归约** | 展开常量定义 |
| **universe** | `Prop`/`Type`/`Type u` 的层级（Sort 0/1/…） |
| **洞** | `#prove` 里未完成的目标（`_`/`?n`），编辑器的状态 |
| **tactic** | 构造证明项的分步工具（intro/apply/exact），不是类型论概念 |
| **递归器** | 归纳原理（`And.rec` 等），手工证明"case 分析"的底层工具 |
| **WHNF** | 弱头范式：头部不再可归约的表达式 |

---

## 11. 原理与致谢

本工具复用了 py_nanobruijn 的真实 Lean 4 内核（de Bruijn 索引 + shift-homomorphic
缓存），教学层零内核改动。定理库移植自
[lean4_lambda_calculator](https://github.com/ColorlessBoy/lean4_lambda_calculator)
的 `query_const.lean`（手工构造的 Prop 逻辑证明集合）。

遇到任何疑惑：`#help`、`#env`、`#print` 是你的朋友。祝你玩得开心。