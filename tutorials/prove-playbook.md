# 🎯 Tactic 草稿模式教学剧本（#prove Playbook）

> 配套工具：教学 REPL 的 `#prove` 模式（`py_nanobruijn/teaching/`）。
> 这些剧本全部经过真实 REPL 验证，可直接复制粘贴运行。

## 怎么用

把每个剧本**逐行**输入 REPL（`proof>` 提示符下）。每行 tactic 后观察三件事：

1. **上下文**——手头有哪些"已知为真"的东西
2. **目标**——还差什么证明
3. **当前项**——证明 lambda 长什么样了（这是最关键的：tactic 在"编辑"这个 lambda）

所有剧本的终点都是 `done` → 合成完整 lambda → 内核检查。

**输入提示**：剧本里的 `forall` 就是 `∀`（纯键盘友好，`∀` 也能打）；`->` 就是 `→`。

---

## 剧本 1：恒等（热身）

```
#prove forall (a : Prop), ∀ (ha : a), a
intro a
intro ha
exact ha
done
```

| 步骤 | 发生什么 |
|---|---|
| `intro a` | 开始 `fun (a : Prop) => _`，目标变 `∀ (ha : a), a` |
| `intro ha` | 项变 `fun (a) => fun (ha : a) => _`，目标变 `a` |
| `exact ha` | 目标正好是 `ha`（`ha : a`），填上 |
| `done` | 完整项：`fun (a : Prop) => fun (ha : a) => ha`，内核通过 |

**教学点**：最朴素的证明 = 直接把参数原样返回。lambda 的每个 binder 对应一次
`intro`。

---

## 剧本 2：蕴含传递（函数复合）

```
#prove forall (a : Prop), ∀ (b : Prop), ∀ (c : Prop), (a -> b) -> (b -> c) -> a -> c
intro a
intro b
intro c
intro fab
intro fbc
intro xa
exact fbc (fab xa)
done
```

| 步骤 | 发生什么 |
|---|---|
| 三个 `intro` | 引入命题 a b c |
| `intro fab` | `fab : a -> b`（手里有"a 蕴含 b"） |
| `intro fbc` | `fbc : b -> c` |
| `intro xa` | `xa : a`——目标变 `c` |
| `exact fbc (fab xa)` | 把 `xa` 喂给 `fab` 得 `b`，再喂给 `fbc` 得 `c` |

完整项：`fun (a) => fun (b) => fun (c) => fun (fab : a -> b) => fun (fbc : b -> c) => fun (xa : a) => fbc (fab xa)`

**教学点**：这正是 `Function.comp` 的 lambda 手写版！`#print Function.comp`
对比一下——你刚用 tactic 写出的项和内核里的定义是**同一种东西**。

---

## 剧本 3：flip（参数交换）

```
#prove forall (a : Prop), ∀ (b : Prop), ∀ (c : Prop), (a -> b -> c) -> b -> a -> c
intro a
intro b
intro c
intro f
intro yb
intro xa
exact f xa yb
done
```

**教学点**：`f : a -> b -> c` 先收 `xa : a` 再收 `yb : b`；目标是 `b -> a -> c`
（顺序交换）——于是 `f xa yb`。对比内置定理 `flip`/`imp.swap` 的证明项。

---

## 剧本 4：三重否定弱化

```
#prove forall (a : Prop), Not (Not (Not a)) -> Not a
intro a
intro hnn
intro ha
exact hnn (fun (hn : a -> False) => hn ha)
done
```

| 步骤 | 发生什么 |
|---|---|
| `intro a` | 目标 `Not (Not (Not a)) -> Not a` |
| `intro hnn` | `hnn : Not (Not (Not a))`——目标变 `Not a` |
| `intro ha` | **关键**：目标 `Not a` 是定义（`a -> False`），`intro` 自动展开它——目标变 `False`，`ha : a` |
| `exact hnn (fun (hn : a -> False) => hn ha)` | `Not X` 定义是 `X -> False`：`hnn` 需要一个 `Not (Not a)` 的证明，给 `fun (hn : a -> False) => hn ha`（一个 `Not a` 的证明：收 `hn : a -> False`，喂 `ha : a` 得 `False`）✓ |

完整项：`fun (a : Prop) => fun (hnn : Not (Not (Not a))) => fun (ha : a) => hnn (fun (hn : a -> False) => hn ha)`

**教学点**：
- `intro` 会先展开定义（`Not a` 变成 `a -> False`）——与真实 Lean 行为一致
- `Not` 是定义不是原语：否定就是"蕴含 False"
- 这个证明的 lambda 形状：最内层 `fun (hn : a -> False) => hn ha` 是 `Not a` 的证明，喂给外层

---

## 剧本 5：合取构造（综合练习）

```
#prove forall (a : Prop), ∀ (b : Prop), ∀ (ha : a), ∀ (hb : b), And a b
intro a
intro b
intro ha
intro hb
apply And.intro
exact ha
exact hb
done
```

| 步骤 | 发生什么 |
|---|---|
| 四个 `intro` | 目标变 `And a b` |
| `apply And.intro` | 用构造子：`And.intro` 的隐式参数 `{a}{b}` 从目标**自动匹配**，显式参数变两个新目标（`_` 和 `?2`） |
| `exact ha` / `exact hb` | 依次填两个目标 |
| `done` | 完整项：`fun ... => @And.intro a b ha hb` |

**教学点**：
- `apply` 是"从目标反推"：目标 `And a b` 告诉我们用 `And.intro` 来构造
- 隐式参数自动匹配（`{a} := a, {b} := b`）——但匹配失败时需要用 `@And.intro` 显式
- `_` 和 `?2` 是"洞"——未完成的目标，`done` 前必须全部填完

---

## 剧本 6：逆否命题（mt 的手写）

```
#prove forall (a : Prop), ∀ (b : Prop), ∀ (f : a -> b), ∀ (hb : Not b), Not a
intro a
intro b
intro f
intro hb
intro ha
exact hb (f ha)
done
```

**教学点**：`hb (f ha)` 的嵌套应用——先 `f` 后 `hb`。对比内置定理 `mt` 的证明项
（`#print mt`），一模一样。证明"如果 a 则 b，且 b 为假，则 a 为假"。

---

## 总结：tactic 与 lambda 的对应关系

| tactic | lambda 结构 |
|---|---|
| `intro x` | `fun (x : A) => _` |
| `apply f` | `@f ... _ ?n` |
| `exact e` | `e` |
| `done` | 合成 + 内核检查 |

**记住**：`done` 之后显示的完整 lambda 项，就是证明本身。tactic 只是写它的工具——
用 `#print` 查看任何内置定理，你会看到同样的 lambda 语言。

## 进阶练习（自己试试）

1. `forall (a : Prop), ∀ (b : Prop), Or a b -> Or b a`（提示：需要 `apply` 之外的工具？——v1 的 `apply` 还不支持 recursor，先用手写 `Or.rec` 体验，或跳过）
2. `forall (a : Prop), a -> a -> a`（两个 `intro` 后选哪个 `exact`？两种答案都对——这是"柯里化"的直观感受）
3. `forall (a : Prop), ∀ (b : Prop), Iff (a -> b) (a -> b)`（`apply Iff.intro` + 两个 `intro` + `exact`）