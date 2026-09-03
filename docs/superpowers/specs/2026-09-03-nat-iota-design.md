# iota 归约 + Nat/算术教学章节 设计文档

日期：2026-09-03
状态：已定稿（用户授权自主推进）

## 背景与问题

py_nanobruijn 内核缺少 iota 归约（recursor 消除规则的计算）。教学影响：

- `#reduce` 无法计算 `Nat.rec` 应用——`2 + 2` 只是"一个表达式"，永远算不出 `4`
- 无法教归纳类型上的计算与归纳证明（算术章节的前提）

**学习者的常见疑问（本设计的教学目标之一）**：为什么之前不需要 iota，现在又必须补？

> 答案：fol 核心的 `Or.rec` 等是 **axiom**——只是"消除规则的名字"。教命题逻辑时
> 一切皆 Prop，`done` 的内核检查靠证明无关性（同命题的证明都相等）短路，内核
> 从不需要"执行"Or.rec。而 Nat 的意义就在于**计算**：`#reduce add two two`
> 要真的出结果，内核必须执行"按 major 前提的构造子分派"这一步——这就是 iota。
> 没有它，`Nat.rec` 永远卡住。这句话会写进 Nat 世界的开场叙事与关卡 hint。

## 方案取舍

- **A. 全量移植 Rust reduce_rec**（K-target、NatLit/StringLit 转换、eta-struct、quot）：
  依赖尚未移植的 mk_elim_level/init_k_target/name_cache 机制，工作量大，教学子集用不到。
- **B. 教学域最小 iota（选定）**：只移植 rec rule 分派核心。`env.get_recursor` 只认
  RecursorDecl——axiom 声明的 Or.rec 天然不会被归约，与现有教学设计零冲突。
- **C. 不实现，Nat 用 axiom 模拟**：无法计算，违背章节目标，否决。

## 内核：reduce_rec（新文件 `tc_rec.py` 或并入 `tc_whnf.py`）

签名与语义镜像 Rust `reduce_rec`（tc.rs:1541），v1 跳过 K/literal/eta-struct：

```python
def reduce_rec(self, const_name, const_levels, args) -> ExprPtr | None:
    rec = self.env.get_recursor(const_name)
    if rec is None or not rec.rules:   # 无规则的 rec（axiom 形状）不归约
        return None
    if len(args) <= rec.major_idx():   # major 前提还没给全
        return None
    major = self.whnf(args[rec.major_idx()])
    major_ctor, major_args = self.ctx.unfold_apps(major)
    rule = next((r for r in rec.rules if r.ctor_name == major_ctor), None)
    if rule is None:
        return None
    extra = len(major_args) - rule.ctor_telescope_size_wo_params   # = num_params（非嵌套）
    r = self.ctx.subst_expr_levels(rule.val, rec.info.uparams, const_levels)
    r = self.ctx.foldl_apps(r, args[:rec.num_params + rec.num_motives + rec.num_minors])
    r = self.ctx.foldl_apps(r, major_args[extra:])
    return self.ctx.foldl_apps(r, args[rec.major_idx() + 1:])
```

挂点：`whnf_no_unfolding_aux` 的 Const 分支（tc_whnf.py:301），在返回卡住结果前尝试
`reduce_rec(name, levels, args)`——与 Rust 的 `reduce_quot || reduce_rec` 分派一致。
quot 分支不移植（教学无 quot 计算）。

## fol 加载器：`inductive` 声明块

teaching/fol/\_\_init\_\_.py 的声明语言扩展（行式，与现风格一致）：

```
inductive Nat : Type
ctor zero : Nat
ctor succ (n : Nat) : Nat
rec Nat.rec {u} : forall {motive : forall (n : Nat), Sort u}, forall (mz : motive zero), forall (ms : forall (n : Nat), forall (ih : motive n), motive (succ n)), forall (t : Nat), motive t
```

装载器行为：

1. 解析 `inductive Name : Ty` → InductiveData（**v1 限制：无参数、无索引、Type 排序**——
   参数化/Prop 排序会引入 elim-level 检查需求，超出本章范围；文档明示）。
   InductiveDecl **先**入 env.declars，使后续 ctor/rec 类型能引用 `Nat`。
2. `ctor name (f1 : T1) ... : Ty` → ConstructorDecl；num_fields = 字段数。
3. `rec Name.rec {u...} : TYPE` → 类型由 parse_expr 解析（学生看得见消除器类型！），
   RecursorData 的 rules 由装载器**综合**（不要求学生手写 de Bruijn 规则）。
4. 规则综合（受限形状）：对 ctor C_i（字段 f1..fn），
   - 规则 rhs 上下文 = [motive, minor_1..minor_k, f1..fn]（minor_j = Var(k-j)，f_i = Var(n-i)）
   - rhs = minor_i 依次应用到各字段；**递归字段**（类型中提到该归纳常量的）在字段参数后
     追加一个递归调用参数：`rec <levels> motive minors... f_i`
   - 例：Nat 的 succ 规则 = `ms n (Nat.rec motive mz ms n)`；Or.inl 规则 = `left h`。
5. 全块就绪后调 `check_inductive_declaration(SimpleNamespace(dag), ind_decl, declars)`
   ——内核真刀真枪验证（类型 Sort 性、ctor 终点、recursor 望远镜、is_rec 标志）。

## nat.fol 片段

依赖 `eq`（拉入 iff）。内容：Nat inductive 块 + 计数常量（one..four，用 succ 链定义，
顺便教 delta）+ `add`（在第一参数上递归：`fun n m => @Nat.rec (fun _ => Nat) m
(fun k ih => succ ih) n`）。不引入 NatLit（那是 nat_extension 快路径，属后续）。

## #reduce 的 iota 步进（teaching/reduce.py）

reduce_steps 重构为显式镜像 whnf 分派：

- delta：头是 Definition → unfold_def（现行为）
- **iota（新）**：头是带 rules 的 RecursorDecl → `reduce_rec` 单步，kind="iota"
- beta：whnf_no_unfolding 收敛（现行为）
- **参数下降（新）**：头卡住但有参数可归约时，下探第一个可归约参数——
  `succ (rec ... one)` 这类后续归约才能继续显示

`ReductionStep.kind` 增加 `'iota'`，show_reduction 配紫色标签。

## Nat 世界（worlds/nat.game，5 关）

`world Nat`，`using: nat`（自动拉入 eq/iff）。开场叙事直接回答
"为什么 Or.rec 不用算而 Nat.rec 必须算"。关卡：

1. **构造**：`Eq Nat (succ zero) (succ zero)` — exact @Eq.refl（热身）
2. **零是右单位**：`∀ (m : Nat), Eq Nat (add zero m) m` — exact @Eq.refl Nat m，
   hint 让学生先 `#reduce add zero m` 亲眼看 iota 把 `add zero m` 算成 `m`
3. **计算演示**：`Eq Nat (add two two) four` — 本世界的招牌关：内核真的算出 4
4. **后继交换**：`∀ (n m : Nat), Eq Nat (add (succ n) m) (succ (add n m))` —
   仍是 refl，因为 iota 会算
5. **第一个归纳证明**：`∀ (n : Nat), Eq Nat (add n zero) n` — n 是变量时 iota 卡住，
   必须用 `@Nat.rec`（显式 motive/mz/ms）做归纳；两块砖都是 Eq.refl——
   "归纳搭骨架，计算填血肉"是本章的点题

hint 中明确写"@Nat.rec 的 motive 决定你要证什么"。

## 测试策略（TDD）

- **Phase 1**（内核）：新建 test_tc_rec.py——手工装 RecursorData：
  zero 规则、succ 规则（含递归调用参数）、major 未给全返回 None、axiom rec 不归约、
  级别替换正确、whnf 端到端 `add`-形状计算
- **Phase 2**（装载器）：test_teaching.TestCore——nat.fol 装载后 declars 含
  InductiveDecl/ConstructorDecl/RecursorDecl；succ 规则 rhs 结构断言；
  `add two two` 经 make_type_checker def_eq `four`
- **Phase 3**（reduce）：TestReduce——iota 步进标签、参数下降、
  `#reduce add two two` 完整归约链
- **Phase 4**（世界）：回放 nat.game 全部关卡（ProofState + done），外加
  test_core_semantic_parity 扩到 nat 片段（若适用）

## 风险与边界

- **真实 Lean export 回归**：ProjFromProp/Wrap.rec 等资源含带规则的 RecursorDecl，
  iota 挂点后 rec 应用可能归约——现有资源没有"应用 rec"的声明，预期零影响；
  全量测试守护
- **终止性**：reduce_rec 内部 `whnf(major)` 递归——与 Rust 相同，timeout 机制兜底
- **教学语法是子集**：参数化/索引/Prop 归纳/嵌套归纳不支持（文档写明），
  不影响本章目标
