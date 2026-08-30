from __future__ import annotations

from ..binder_style import BinderStyle
from ..name import Name
from ..ptr import ExprPtr
from .core import BootstrapCore
from .parser import parse_expr, parse_expr_with_context
from .pretty import _Pretty, pretty


class Hole:
    """一个未完成的目标。

    ctx  = 局部变量 (name, style, ty)，outer → inner（最内层为 var 0）
    goal = 待证类型（在 ctx 下开放）
    """

    __slots__ = ('ctx', 'goal', 'id')

    def __init__(self, hole_id: int, ctx: list, goal: ExprPtr):
        self.id = hole_id
        self.ctx = ctx
        self.goal = goal


class _Node:
    """部分证明项节点基类（教学层维护的编辑状态，非内核概念）。"""


class HoleNode(_Node):
    """洞标记：`_`（当前洞）或 `?id`（未填洞）。内容实时查 subholes[id]。"""

    __slots__ = ('hole_id',)

    def __init__(self, hole_id: int):
        self.hole_id = hole_id


class IntroNode(_Node):
    __slots__ = ('body', 'name', 'style', 'ty')

    def __init__(self, name: str, style: BinderStyle, ty: ExprPtr, body: _Node):
        self.name = name
        self.style = style
        self.ty = ty
        self.body = body


class AppNode(_Node):
    __slots__ = ('arg', 'fun')

    def __init__(self, fun: _Node, arg: _Node):
        self.fun = fun
        self.arg = arg


class ExactNode(_Node):
    __slots__ = ('expr',)

    def __init__(self, expr: ExprPtr):
        self.expr = expr


class ProofState:
    """#prove 草稿模式：洞 + 部分证明项树。

    - subholes[id] = 洞 id 的当前部分项（父节点只持有 HoleNode(id) 标记，
      内容始终查 subholes —— 无陈旧引用问题）
    - 当前洞 = 第一个（按创建顺序）仍未填充的洞（线性目标栈）
    - intro 在 HoleNode(id) 叶处包裹 IntroNode；apply/exact 替换该叶
    """

    def __init__(self, core: BootstrapCore, goal_ty: ExprPtr,
                 timeout_secs: float = 0.0, color: bool = False):
        self.core = core
        self.ctx = core.ctx
        self.goal_ty = goal_ty
        self.timeout_secs = float(timeout_secs)
        self.color = color
        self.holes: list[Hole] = [Hole(0, [], goal_ty)]
        self.subholes: dict[int, _Node] = {0: HoleNode(0)}
        self._next_hole_id = 1

    # ---------- 展示 ----------

    def _pp(self, e: ExprPtr, names) -> str:
        return _Pretty(self.core, self.color)._pp(e, tuple(names))

    def _current_hole(self) -> Hole | None:
        for h in self.holes:
            if self._tree_contains(self.subholes[h.id], h.id):
                return h
        return None

    def _require_hole(self) -> Hole:
        hole = self._current_hole()
        if hole is None:
            raise ValueError("当前没有未完成的目标（全部已填充，运行 done 结束证明）")
        return hole

    def _tree_contains(self, node: _Node, hole_id: int) -> bool:
        if isinstance(node, HoleNode):
            return node.hole_id == hole_id
        if isinstance(node, IntroNode):
            return self._tree_contains(node.body, hole_id)
        if isinstance(node, AppNode):
            return (self._tree_contains(node.fun, hole_id)
                    or self._tree_contains(node.arg, hole_id))
        return False

    def _replace_hole(self, node: _Node, hole_id: int, new_node: _Node) -> _Node:
        """把树中 HoleNode(hole_id) 叶替换为 new_node（其余节点按引用保留）。"""
        if isinstance(node, HoleNode):
            if node.hole_id == hole_id:
                return new_node
            return node
        if isinstance(node, IntroNode):
            return IntroNode(node.name, node.style, node.ty,
                             self._replace_hole(node.body, hole_id, new_node))
        if isinstance(node, AppNode):
            return AppNode(self._replace_hole(node.fun, hole_id, new_node),
                           self._replace_hole(node.arg, hole_id, new_node))
        return node

    def _render(self, node: _Node, names: tuple[str, ...], current_id: int) -> str:
        if isinstance(node, HoleNode):
            if self._tree_contains(self.subholes[node.hole_id], node.hole_id):
                if node.hole_id == current_id:
                    return "_"
                return f"?{node.hole_id}"
            return self._render(self.subholes[node.hole_id], names, current_id)
        if isinstance(node, IntroNode):
            open_b, close_b = ("{", "}") if node.style == BinderStyle.IMPLICIT else ("(", ")")
            return (f"fun {open_b}{node.name} : {self._pp(node.ty, names)}{close_b} => "
                    f"{self._render(node.body, names + (node.name,), current_id)}")
        if isinstance(node, AppNode):
            fun_str = self._render(node.fun, names, current_id)
            if isinstance(node.fun, ExactNode) and self._const_is_implicit_first(node.fun.expr):
                fun_str = f"@{fun_str}"
            return f"{fun_str} {self._render(node.arg, names, current_id)}"
        if isinstance(node, ExactNode):
            return self._pp(node.expr, names)
        raise ValueError(f"render: unknown node {type(node).__name__}")

    def _const_is_implicit_first(self, e: ExprPtr) -> bool:
        v = self.ctx.view_expr(e)
        if v.tag != 'Const':
            return False
        info = self.core.env.get_declar(v.name).info
        ty_v = self.ctx.view_expr(ExprPtr.closed(info.ty))
        return ty_v.tag == 'Pi' and ty_v.binder_style == BinderStyle.IMPLICIT

    def context(self) -> str:
        hole = self._current_hole()
        if hole is None:
            term = self._render(self.subholes[0], (), -1)
            return f"所有目标已完成，请运行 done\n当前项: {term}"
        names: list[str] = []
        ctx_lines = []
        for (name, _style, ty) in hole.ctx:
            ctx_lines.append(f"{name} : {self._pp(ty, names)}")
            names.append(name)
        ctx_str = "（空）" if not ctx_lines else ", ".join(ctx_lines)
        goal = self._pp(hole.goal, names)
        term = self._render(self.subholes[0], (), hole.id)
        return f"上下文: {ctx_str}\n目标: {goal}\n当前项: {term}"

    # ---------- intro ----------

    def intro(self, names: str | None = None) -> str:
        """目标为 Pi 时把 binder 加入上下文（可连写 `intro a b c`）。"""
        hole = self._require_hole()
        wanted = names.split() if names else []
        tc = self.core.make_type_checker()
        # 洞上下文入栈，使 whnf 的深度与目标的变量引用一致
        for (_, _, bt) in hole.ctx:
            tc.push_local(bt)
        for given in wanted or [None]:
            # 先 whnf 目标（如 Not a 定义展开为 a -> False），对齐真实 Lean intro 行为
            goal_whnf = tc.whnf(hole.goal)
            u = self.ctx.unfold_pi(goal_whnf)
            if u is None:
                goal_str = self._pp(hole.goal, [n for (n, _, _) in hole.ctx])
                raise ValueError(
                    f"intro: 目标不是函数类型，无法 intro（当前目标: {goal_str}）")
            name_ptr, style, bt, body = u
            if given is None:
                if self.ctx.dag.get_name(name_ptr).is_anon():
                    raise ValueError("intro: 匿名 binder 需要名字（如 intro x）")
                bname = self.ctx.name_to_string(name_ptr)
            else:
                bname = given
            hole.ctx.append((bname, style, bt))
            hole.goal = body
            self.subholes[hole.id] = self._replace_hole(
                self.subholes[hole.id], hole.id,
                IntroNode(bname, style, bt, HoleNode(hole.id)))
            tc.push_local(bt)
        return self.context()

    # ---------- apply ----------

    def apply(self, f: str) -> str:
        """用常量 f 匹配目标：隐式参数从目标参数对齐取值，显式参数变为新目标。

        模式匹配只做头部对齐（头部常量名 + 层级 + 参数数量相同），不做 unification。
        """
        hole = self._require_hole()
        fexpr = parse_expr(self.core, f)
        v = self.ctx.view_expr(fexpr)
        if v.tag != 'Const':
            raise ValueError("apply: 只支持常量，如 And.intro")
        tc = self.core.make_type_checker(self.timeout_secs)
        f_ty = tc.infer(fexpr, 'infer_only')
        last_id = hole.id
        chain: list[tuple[str, BinderStyle, ExprPtr]] = []
        cur = f_ty
        while True:
            u = self.ctx.unfold_pi(cur)
            if u is None:
                break
            name_ptr, style, bt, body = u
            chain.append((self.ctx.name_to_string(name_ptr), style, bt))
            cur = body
        result = cur
        r_head, r_args = self.ctx.unfold_apps(result)
        c_head, c_args = self.ctx.unfold_apps(hole.goal)
        r_hv = self.ctx.view_expr(r_head)
        c_hv = self.ctx.view_expr(c_head)
        hole_names = [n for (n, _, _) in hole.ctx]
        chain_names = [n for (n, _, _) in chain]
        if (r_hv.tag != 'Const' or c_hv.tag != 'Const'
                or r_hv.name != c_hv.name
                or self.core.dag.uparams[r_hv.const_levels]
                != self.core.dag.uparams[c_hv.const_levels]
                or len(r_args) != len(c_args)):
            raise ValueError(
                f"apply {f}: 目标头部 ({self._pp(hole.goal, hole_names)}) 与 {f} 的结果 "
                f"({self._pp(result, chain_names)}) 不匹配"
                f"（提示：可尝试 apply @{f} 或检查目标）")
        n_chain = len(chain)
        values: dict[int, ExprPtr] = {}
        for i, r_arg in enumerate(r_args):
            rv = self.ctx.view_expr(r_arg)
            if rv.tag != 'Var':
                if r_arg.is_closed():
                    continue  # 常量参数（如 propext 里的 Prop），无需模式匹配
                raise ValueError(
                    f"apply {f}: 结果类型的参数不是变量，无法自动匹配"
                    f"（提示：可尝试 apply @{f}）")
            j = n_chain - 1 - rv.dbj_idx
            if j < 0 or j >= n_chain:
                raise ValueError(f"apply {f}: 结果类型引用了未知参数（提示：可尝试 apply @{f}）")
            name, style, bt = chain[j]
            if style == BinderStyle.IMPLICIT:
                # 隐式参数是模式变量：值取自目标对应位置的子项。
                # 仅自动填充 SIMPLE 类型（Prop/Sort/变量）——复合类型（如
                # motive : And a b -> Sort u）在 open 上下文经内核 inst 路径
                # 是已知缺陷（test_imp_swap_known_kernel_issue），教学层不
                # 走那条路，提示改用 @Const 显式传参。
                bt_v = self.ctx.view_expr(bt)
                if bt_v.tag == 'Pi':
                    raise ValueError(
                        f"apply {f}: {f} 的隐式参数 {name} 是复合类型，教学模式暂不支持自动填充"
                        f"——请用 @{f} 显式传参")
            # DEFAULT binder 出现在结果类型里时同样由目标对齐确定（如
            # Eq.refl 的 a : α 出现在 Eq α a a 里），不作为新目标。
            values[j] = c_args[i]
        for j, (name, style, _bt) in enumerate(chain):
            if style == BinderStyle.IMPLICIT and j not in values:
                raise ValueError(
                    f"apply {f}: 无法确定 {f} 的隐式参数 {name}（未出现在结果类型中）")
        args: list[_Node] = []
        for k, (name, style, bt) in enumerate(chain):
            if k in values:
                args.append(ExactNode(values[k]))
            elif style == BinderStyle.IMPLICIT:
                raise AssertionError(f"apply {f}: 隐式参数 {name} 未确定（内部错误）")
            else:
                goal = self._instantiate_binder_type(bt, k, values, f)
                new_id = self._new_hole(list(hole.ctx), goal, after=last_id)
                last_id = new_id
                args.append(HoleNode(new_id))
        node: _Node = ExactNode(fexpr)
        for a in args:
            node = AppNode(node, a)
        self.subholes[hole.id] = self._replace_hole(self.subholes[hole.id], hole.id, node)
        return self.context()

    def _new_hole(self, ctx: list, goal: ExprPtr, after: int | None = None) -> int:
        new_id = self._next_hole_id
        self._next_hole_id += 1
        hole = Hole(new_id, ctx, goal)
        if after is None:
            self.holes.append(hole)
        else:
            # 插入到 after 洞之后：cases 的 case-洞是当前洞的延续，
            # 应优先于兄弟洞（如 Iff.intro 的 mpr）被填充。
            idx = next(i for i, h in enumerate(self.holes) if h.id == after)
            self.holes.insert(idx + 1, hole)
        self.subholes[new_id] = HoleNode(new_id)
        return new_id

    def _instantiate_binder_type(self, bt: ExprPtr, k: int,
                                 values: dict[int, ExprPtr], f: str) -> ExprPtr:
        """把 binder 类型（链位置 k，作用域 = 链 binder 0..k-1）里已由目标对齐
        确定的参数（隐式参数 + 出现在结果类型里的显式参数）替换为对应值，
        得到新洞的目标。

        不用内核 inst/inst_beta：
        1. inst_beta 只替换「最内层连续 binder 块」，无法跳过夹在中间的 DEFAULT
           binder（如 And.intro 的 hb : b 在 [a, b, ha] 作用域里是 var1，而 var0
           是 DEFAULT 的 ha）——位置语义对不上；
        2. 嵌套 Pi 经 inst_beta/inst 是已知内核缺陷路径
           （test_imp_swap_known_kernel_issue）。
        这里用 view + mk_* 手工按 de Bruijn 索引替换，只依赖安全的构造原语。
        """
        return self._subst_chain(bt, k, values, f)

    def _subst_chain(self, e: ExprPtr, k: int,
                     values: dict[int, ExprPtr], f: str) -> ExprPtr:
        v = self.ctx.view_expr(e)
        tag = v.tag
        if tag == 'Var':
            j = k - 1 - v.dbj_idx
            if j in values:
                return values[j]
            raise ValueError(
                f"apply {f}: 暂不支持（{f} 的参数类型引用了其它显式参数，无法自动填充）")
        if tag == 'App':
            return self.ctx.mk_app(
                self._subst_chain(v.fun, k, values, f),
                self._subst_chain(v.arg, k, values, f))
        if tag in ('Pi', 'Lambda'):
            bt2 = self._subst_chain(v.binder_type, k, values, f)
            body2 = self._subst_chain(v.body, k + 1, values, f)
            # mk_pi/mk_lambda 约定 body 位于 binder 之内（深度 +1，var 0 = binder 自身）
            body2 = body2.shift_up(1)
            if tag == 'Pi':
                return self.ctx.mk_pi(v.binder_name, v.binder_style, bt2, body2)
            return self.ctx.mk_lambda(v.binder_name, v.binder_style, bt2, body2)
        if tag == 'Let':
            return self.ctx.mk_let(
                v.binder_name,
                self._subst_chain(v.binder_type, k, values, f),
                self._subst_chain(v.val, k, values, f),
                self._subst_chain(v.body, k + 1, values, f).shift_up(1))
        if tag == 'Proj':
            return self.ctx.mk_proj(
                v.ty_name, v.proj_idx,
                self._subst_chain(v.structure, k, values, f))
        return e

    # ---------- exact ----------

    def exact(self, expr_text: str) -> str:
        """当前洞用表达式精确填充：在内核检查 e : 目标（上下文 = 洞的 ctx）。"""
        hole = self._require_hole()
        names = [n for (n, _, _) in hole.ctx]
        e = parse_expr_with_context(self.core, expr_text, names)
        tc = self.core.make_type_checker(self.timeout_secs)
        for (_name, _style, ty) in hole.ctx:
            tc.push_local(ty)
        try:
            inferred = tc.infer(e, 'check')
        except ValueError as err:
            raise ValueError(f"exact: {err}") from None
        if not tc.is_def_eq(inferred, hole.goal):
            raise ValueError(
                f"exact: 类型不匹配：{expr_text} : {self._pp(inferred, names)}，"
                f"目标为 {self._pp(hole.goal, names)}")
        self.subholes[hole.id] = self._replace_hole(self.subholes[hole.id], hole.id,
                                                    ExactNode(e))
        return self.context()

    # ---------- cases ----------

    def cases(self, h_name: str) -> str:
        """对上下文变量 h 做情形分析（自动构造 recursor 应用）。

        - h : And a b  → 1 个新目标（上下文 + ha : a, hb : b）
        - h : Or a b   → 2 个分支目标（左 h1 : a / 右 h2 : b）
        - h : False    → 目标直接完成（exfalso）
        - h : Exists p → 1 个新目标（上下文 + x : α, hx : p x）

        教学叙事：cases 显示 rec 骨架（@And.rec a b (fun _ => ?goal) _ h），
        分支洞逐个填充——tactic 只是编辑证明项，rec 才是本质。
        """
        hole = self._require_hole()
        h_ty = self._lookup_ctx_type(hole, h_name)
        head, args = self.ctx.unfold_apps(h_ty)
        hv = self.ctx.view_expr(head)
        if hv.tag != 'Const':
            raise ValueError(
                f"cases {h_name}: {h_name} 的类型不是 And/Or/False/Exists"
                f"（当前: {self._pp(h_ty, [n for (n, _, _) in hole.ctx])}）")
        kind = self.ctx.name_to_string(hv.name)
        if kind not in ('And', 'Or', 'False', 'Exists'):
            raise ValueError(f"cases {h_name}: 暂不支持类型 {kind}")
        min_args = {'And': 2, 'Or': 2, 'Exists': 2, 'False': 0}[kind]
        if len(args) < min_args:
            raise ValueError(
                f"cases {h_name}: {h_name} 的类型是 {kind} 的部分应用"
                f"（请用 @{kind}.{{u}} α p 等显式写全类型参数）")
        h_idx = self._ctx_index(hole, h_name)
        h_ref = self.ctx.mk_var(h_idx)  # h 的变量引用（ctx 内）
        c_goal = hole.goal

        if kind == 'And':
            a, b = args[0], args[1]
            motive = self._motive(h_ty, c_goal)
            new_id = self._new_hole(
                list(hole.ctx) + [("ha", BinderStyle.DEFAULT, a.shift_up(1)),
                                  ("hb", BinderStyle.DEFAULT, b.shift_up(2))],
                c_goal.shift_up(2), after=hole.id)
            case_node = IntroNode("ha", BinderStyle.DEFAULT, a.shift_up(1),
                                   IntroNode("hb", BinderStyle.DEFAULT,
                                             b.shift_up(2), HoleNode(new_id)))
            rec = self._rec_app(self.core.name_to_ptr("And.rec"), (0,),
                                [a.shift_up(1), b.shift_up(1), motive, h_ref,
                                 case_node])
            self.subholes[hole.id] = self._replace_hole(
                self.subholes[hole.id], hole.id, rec)
        elif kind == 'Or':
            a, b = args[0], args[1]
            motive = self._motive(h_ty, c_goal)
            left_id = self._new_hole(
                list(hole.ctx) + [("h1", BinderStyle.DEFAULT, a.shift_up(1))],
                c_goal.shift_up(1), after=hole.id)
            right_id = self._new_hole(
                list(hole.ctx) + [("h2", BinderStyle.DEFAULT, b.shift_up(1))],
                c_goal.shift_up(1), after=left_id)
            rec = self._rec_app(self.core.name_to_ptr("Or.rec"), (0,),
                                [a.shift_up(1), b.shift_up(1), motive,
                                 IntroNode("h1", BinderStyle.DEFAULT, a.shift_up(1),
                                           HoleNode(left_id)),
                                 IntroNode("h2", BinderStyle.DEFAULT, b.shift_up(1),
                                           HoleNode(right_id)),
                                 h_ref])
            self.subholes[hole.id] = self._replace_hole(
                self.subholes[hole.id], hole.id, rec)
        elif kind == 'False':
            motive = self._motive(h_ty, c_goal)
            rec = self._rec_app(self.core.name_to_ptr("False.rec"), (0,),
                                [motive, h_ref])
            self.subholes[hole.id] = self._replace_hole(
                self.subholes[hole.id], hole.id, rec)
        else:  # Exists
            alpha, p = args[0], args[1]
            u = self.ctx.dag.uparams[hv.const_levels]
            motive = self._motive(h_ty, c_goal)
            new_id = self._new_hole(
                list(hole.ctx) + [("x", BinderStyle.DEFAULT, alpha.shift_up(1)),
                                  ("hx", BinderStyle.DEFAULT,
                                   self.ctx.mk_app(p.shift_up(2), self.ctx.mk_var(0)))],
                c_goal.shift_up(2), after=hole.id)
            case_node = IntroNode("x", BinderStyle.DEFAULT, alpha.shift_up(1),
                                   IntroNode("hx", BinderStyle.DEFAULT,
                                             self.ctx.mk_app(p.shift_up(2),
                                                             self.ctx.mk_var(0)),
                                             HoleNode(new_id)))
            rec = self._rec_app(self.core.name_to_ptr("Exists.rec"), tuple(u),
                                [alpha.shift_up(1), p.shift_up(1), motive,
                                 case_node, h_ref])
            self.subholes[hole.id] = self._replace_hole(
                self.subholes[hole.id], hole.id, rec)
        return self.context()

    def _lookup_ctx_type(self, hole: Hole, name: str) -> ExprPtr:
        for (n, _style, ty) in reversed(hole.ctx):
            if n == name:
                return ty
        raise ValueError(f"cases {name}: 上下文中没有变量 {name!r}")

    def _ctx_index(self, hole: Hole, name: str) -> int:
        """ctx 变量从内到外的 var 索引（最内层 = 0）。"""
        for i, (n, _style, _ty) in enumerate(reversed(hole.ctx)):
            if n == name:
                return i
        raise AssertionError(f"cases {name}: 变量不在上下文（内部错误）")

    def _motive(self, h_ty: ExprPtr, c_goal: ExprPtr) -> ExprPtr:
        """rec 的 motive：fun (anon : h 的类型) => 当前目标（提升 1 层）。"""
        anon = self.ctx.dag.insert_name(Name.anon())
        return self.ctx.mk_lambda(anon, BinderStyle.DEFAULT, h_ty.shift_up(1),
                                  c_goal.shift_up(1))

    def _rec_app(self, rec_name, levels: tuple, args: list) -> _Node:
        """构造 rec 常量应用的 _Node 链。levels 为显式 universe 层级（空 = 默认 0 或常量自带）。"""
        if levels:
            rec_const = self.ctx.mk_const(rec_name, self.ctx.dag.insert_uparams(levels))
        else:
            rec_const = self.ctx.mk_const(rec_name, self.ctx.dag.insert_uparams(()))
        node: _Node = ExactNode(rec_const)
        for a in args:
            node = AppNode(node, a if isinstance(a, _Node) else ExactNode(a))
        return node

    # ---------- done ----------

    def done(self) -> str:
        unfilled = [h.id for h in self.holes
                    if self._tree_contains(self.subholes[h.id], h.id)]
        if unfilled:
            raise ValueError(f"done: 还有 {len(unfilled)} 个目标未完成")
        term = self.synthesize()
        tc = self.core.make_type_checker(self.timeout_secs)
        try:
            inferred = tc.infer(term, 'check')
            tc.assert_def_eq(inferred, self.goal_ty)
        except ValueError as err:
            raise ValueError(f"done: 内核检查失败: {err}") from None
        return f"完整证明项:\n{pretty(self.core, term, self.color)}\n内核检查: 通过"

    # ---------- 合成 ----------

    def synthesize(self) -> ExprPtr:
        """部分证明项树 → ExprPtr（所有洞必须已填充）。"""
        return self._synth(self.subholes[0])

    def _synth(self, node: _Node) -> ExprPtr:
        if isinstance(node, HoleNode):
            inner = self.subholes[node.hole_id]
            if isinstance(inner, HoleNode):
                raise TypeError(f"synthesize: hole ?{node.hole_id} 未填充")
            return self._synth(inner)
        if isinstance(node, IntroNode):
            return self.ctx.mk_lambda(self.core.name_to_ptr(node.name), node.style,
                                      node.ty, self._synth(node.body))
        if isinstance(node, AppNode):
            return self.ctx.mk_app(self._synth(node.fun), self._synth(node.arg))
        if isinstance(node, ExactNode):
            return node.expr
        raise ValueError(f"synthesize: unknown node {type(node).__name__}")