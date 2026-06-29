# 第八讲 Parser — 导出文件解析

Parser 是 nanobruijn 的前端——它将 Lean 编译器输出的 export 文件（NDJSON 格式）反序列化为内部数据结构（Name、Level、Expr DAG、Declar），产出 `ExportFile` 供后续类型检查使用。

对应文件：`py_nanobruijn/parser.py`（604 行）

## 整体流程

```
.lean 源文件
  ↓  Lean 编译器
.export 文件（NDJSON，每行一个 JSON 对象）
  ↓
Parser.feed_line(line)     ← 逐行处理
  ├── meta                 → 版本检查
  ├── name_str / name_num  → DAG 中插入 Name
  ├── il (level)           → DAG 中插入 Level
  ├── ie (expr)            → DAG 中插入 Expr（含 OSNF 优化）
  └── axiom/thm/def/opaque
      /quot/inductive       → 构造 Declar，加入 declars
  ↓
Parser.finalize()
  ↓
ExportFile(dag, declars, config, skipped)
  ↓
check_all_declars()         ← 第七讲
```

Export 文件是逐行 NDJSON，每行是一个独立的对象，通过 `"in"`、`"il"`、`"ie"` 等键标记类型。实体之间通过**导出索引**（非负整数）相互引用——Parser 用 remap 数组将这些索引翻译为 DAG 指针。

## Parser 类结构

```python
class Parser:
    def __init__(self, dag: LeanDag, config):
        self.dag = dag
        self.config = config
        self.declars: Dict[int, Declar] = {}        # 解析出的所有声明
        self.skipped: List[str] = []                 # 被跳过的声明名字
        self.name_remap: List[int] = [0]             # 导出索引 → DAG Name 索引
        self.level_remap: List[int] = [0]            # 导出索引 → DAG Level 索引
        self.expr_remap: List[Tuple[int, int]] = [(0, 0)]  # 导出索引 → (core, shift)
        self.osnf_count = 0                          # OSNF 命中计数器
```

三个 remap 数组是 Parser 的核心。Export 文件中，每个 name / level / expr 实体都有一个导出索引（`"in"`、`"il"`、`"ie"`），后续实体通过这个索引引用它们。Parser 在处理每个实体时，把该索引映射到 DAG 中的位置，存入 remap 数组。

```
export index 42  ───→  name_remap[42] = dag_index_157
```

## feed_line — 主分派

```python
def feed_line(self, line: str):
    obj = json.loads(line)
    if "meta" in obj:
        self._handle_meta(obj["meta"])
    elif "in" in obj:
        inner = obj.get("str")
        if inner is not None:
            self._handle_name_str(obj)       # 字符串名字
        elif obj.get("num") is not None:
            self._handle_name_num(obj)       # 数值名字
        else:
            raise ValueError(...)
    elif "il" in obj:
        self._handle_level(obj)              # 宇宙层级
    elif "ie" in obj:
        self._handle_expr(obj)               # 表达式
    elif "axiom" in obj:
        self._handle_axiom(obj["axiom"])
    elif "thm" in obj:
        self._handle_thm(obj["thm"])
    elif "def" in obj:
        self._handle_def(obj["def"])
    elif "opaque" in obj:
        self._handle_opaque(obj["opaque"])
    elif "quot" in obj:
        self._handle_quot(obj["quot"])
    elif "inductive" in obj:
        self._handle_inductive(obj["inductive"])
    else:
        raise ValueError(f"Unknown line: {obj}")
```

解析是**单遍顺序**的——实体必须先定义后引用。Name 和 Level 必须先于引用它们的 Expr，Expr 必须先于引用它们的 Declar。

### Meta — 版本检查

```python
def _handle_meta(self, meta: dict):
    format_ver = meta.get("format", {}).get("version", "0.0.0")
    parts = format_ver.split(".")
    major, minor, _ = int(parts[0]), int(parts[1]), int(parts[2])
    if major < 3 or (major == 3 and minor < 1):
        raise ValueError(f"version {format_ver} < min supported 3.1.0")
    if major > 3 or (major == 3 and minor >= 2):
        raise ValueError(f"version {format_ver} >= max supported 3.2.0")
```

只接受 3.1.x 系列的 export 格式。

## remap 机制

每个实体类型有自己的 remap 数组，由三个 getter 封装查找逻辑：

```python
def get_name_ptr(self, idx: int) -> int:
    dag_idx = self.name_remap[idx] if idx < len(self.name_remap) else -1
    if dag_idx == -1:
        raise ValueError(f"export references name index {idx} before it is defined")
    return dag_idx

def get_level_ptr(self, idx: int) -> int:
    dag_idx = self.level_remap[idx] if idx < len(self.level_remap) else -1
    if dag_idx == -1:
        raise ValueError(...)
    return dag_idx

def get_expr_ptr(self, idx: int) -> ExprPtr:
    if idx >= len(self.expr_remap):
        dag_idx, shift = -1, 0
    else:
        dag_idx, shift = self.expr_remap[idx]
    if dag_idx == -1:
        raise ValueError(...)
    if shift == CLOSED_SHIFT:
        return ExprPtr.closed(dag_idx)
    return ExprPtr(dag_idx, shift)
```

关键点：Expr 的 remap 存储的是 `(core, shift)` 对——表达式在 DAG 中总是以最小 shift 存储（OSNF），外部 shift 单独记录。

辅助方法 `get_core_ptr` 要求引用的是闭项（如声明类型和定义体）：

```python
def get_core_ptr(self, idx: int) -> int:
    ep = self.get_expr_ptr(idx)
    if not ep.is_closed():
        raise ValueError(f"expected closed expression, got shift={ep.shift}")
    return ep.core
```

## Name 解析

Name 有两种变体：

```python
def _handle_name_str(self, obj: dict):
    export_idx = obj["in"]
    pre = obj["str"]["pre"]      # 前缀名字的导出索引
    s = obj["str"]["str"]        # 字符串片段
    pfx = self.get_name_ptr(pre)
    sfx = self.dag.insert_string(s)
    dag_idx = self.dag.insert_name(Name.str(pfx, sfx))
    self.name_remap[export_idx] = dag_idx

def _handle_name_num(self, obj: dict):
    export_idx = obj["in"]
    pre = obj["num"]["pre"]
    i = obj["num"]["i"]
    pfx = self.get_name_ptr(pre)
    dag_idx = self.dag.insert_name(Name.num(pfx, i))
    self.name_remap[export_idx] = dag_idx
```

Name 是前缀树——每个名字的 `pre` 引用其父名字的导出索引，`str`/`num` 是本层片段。例如 `Nat.add` 的导出表示为 `pre=Nat的索引, str="add"`。

## Level 解析

Level 有四种变体：

```python
def _handle_level(self, obj: dict):
    export_idx = obj["il"]
    if "succ" in obj:
        pred = self.get_level_ptr(obj["succ"])
        dag_idx = self.dag.insert_level(Level.succ(pred))
    elif "max" in obj:
        lv, rv = obj["max"]
        lv = self.get_level_ptr(lv)
        rv = self.get_level_ptr(rv)
        dag_idx = self.dag.insert_level(Level.max(lv, rv))
    elif "imax" in obj:
        lv, rv = obj["imax"]
        lv = self.get_level_ptr(lv)
        rv = self.get_level_ptr(rv)
        dag_idx = self.dag.insert_level(Level.imax(lv, rv))
    elif "param" in obj:
        name_ptr = self.get_name_ptr(obj["param"])
        dag_idx = self.dag.insert_level(Level.param(name_ptr))
    else:
        raise ValueError(f"Unknown level variant: {obj}")
    self.level_remap[export_idx] = dag_idx
```

每种变体的子表达式通过 `get_level_ptr` 递归引用已解析的 Level。

## Expr 解析 — 十种变体

表达式解析是 parser 中最复杂的部分。每种变体都需要：
1. `get_expr_ptr` 获取子表达式的 `(core, shift)`
2. 计算 `eff`（有效 binder 数量）和 `min_shift`（OSNF 优化）
3. 构建 `Expr` 并插入 DAG
4. 写入 `expr_remap[export_idx] = (dag_idx, min_shift)`

### 简单变体（无子表达式）

```python
def _handle_expr(self, obj: dict):
    export_idx = obj["ie"]

    if "sort" in obj:
        level = self.get_level_ptr(obj["sort"])
        dag_idx, _ = self.dag.insert_expr(Expr.sort(level))
        self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)

    elif "bvar" in obj:
        dbj_idx = obj["bvar"]
        var0_idx = self._find_or_insert_var0()
        self.expr_remap[export_idx] = (var0_idx, dbj_idx)
```

**Sort**：`Sort u` 是闭项，shift = CLOSED_SHIFT。

**bvar**：de Bruijn 索引 `i` 表示为 `Var(0)↑ⁱ`——即 DAG 中存 `Var(0)` 的索引，shift 就是索引值。`_find_or_insert_var0` 确保 `Var(0)` 在 DAG 中存在。

```python
def _find_or_insert_var0(self) -> int:
    var0 = Expr.var(0)
    idx = self.dag.expr_map.get(var0)
    if idx is not None:
        return idx
    idx, _ = self.dag.insert_expr(var0)
    return idx
```

```python
    elif "const" in obj:
        c = obj["const"]
        name = self.get_name_ptr(c["name"])
        levels = self.get_levels_ptr(c.get("us", []))
        dag_idx, _ = self.dag.insert_expr(Expr.const(name, levels))
        self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)
```

**Const**：常量引用（如 `Nat`、`Nat.add`），是闭项。`levels` 是 universe 层级参数列表（`List.{u}` 中的 `u`）。

```python
    elif "strVal" in obj:
        ...
        dag_idx, _ = self.dag.insert_expr(Expr.string_lit(string_ptr))
        self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)

    elif "natVal" in obj:
        ...
        dag_idx, _ = self.dag.insert_expr(Expr.nat_lit(bigint_ptr))
        self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)

    elif "mdata" in obj:
        raise ValueError("Expr.mdata not supported")
```

**strVal / natVal**：字面量开关由 `config` 控制。mdata 元数据暂不支持。

### 复杂变体（OSNF 优化）

App、forallE（Pi）、lam（Lambda）、letE、proj 共享 OSNF 模式。它们的共同结构是：

```
1. 获取所有子表达式的 (core, shift)
2. 计算每个子表达式的有效 binder 数 eff
3. 如果 eff > 0，则 eff = core_nlbv + shift（有自由变量的情况下）
4. 如果 eff == 0，则该子表达式是闭项，不参与 min_shift 计算
5. 取所有非闭子表达式的 shift 的最小值作为 min_shift
6. 如果 0 < min_shift < CLOSED_SHIFT，osnf_count++
7. 从每个非闭子表达式的 shift 中减去 min_shift
8. 用归一化后的子表达式构建 Expr，插入 DAG
9. expr_remap 中整体 shift 记为 min_shift
```

以 App 为例：

```python
    elif "app" in obj:
        a = obj["app"]
        fun_e = self.get_expr_ptr(a["fn"])
        arg_e = self.get_expr_ptr(a["arg"])

        fun_core_nlbv = self._num_loose_bvars(fun_e.core)
        arg_core_nlbv = self._num_loose_bvars(arg_e.core)
        fun_eff = 0 if fun_core_nlbv == 0 else fun_core_nlbv + fun_e.shift
        arg_eff = 0 if arg_core_nlbv == 0 else arg_core_nlbv + arg_e.shift

        if fun_eff == 0 and arg_eff == 0:
            min_shift = CLOSED_SHIFT
        elif fun_eff == 0:
            min_shift = arg_e.shift
        elif arg_eff == 0:
            min_shift = fun_e.shift
        else:
            min_shift = min(fun_e.shift, arg_e.shift)

        if 0 < min_shift < CLOSED_SHIFT:
            self.osnf_count += 1

        core_fun = fun_e if fun_eff == 0 else ExprPtr(fun_e.core, fun_e.shift - min_shift)
        core_arg = arg_e if arg_eff == 0 else ExprPtr(arg_e.core, arg_e.shift - min_shift)

        dag_idx, _ = self.dag.insert_expr(Expr.app(core_fun, core_arg))
        self.expr_remap[export_idx] = (dag_idx, min_shift)
```

**为什么需要 OSNF？**

考虑表达式 `(λx. λy. x) a b`。在 export 格式中，`x` 和 `y` 是 binder 深度 2 和 1 的自由变量。如果不做 shift 归一化，DAG 中同一个表达式核心会因为不同 binder 上下文而出现多次，浪费 DAG 的 hash-consing。

OSNF 把所有子表达式拉到最小的公共 shift，确保 DAG 中相同核心只存一次。

forallE、lam、letE 的模式与 app 类似，但 binder 会引入一个额外的深度（body 的有效 shift 比子表达式多 1）：

```python
    elif "forallE" in obj:     # Pi
        ...
        body_eff = 0 if body_core_nlbv == 0 else body_core_nlbv + body_e.shift
        body_outer = None if body_eff <= 1 else body_e.shift - 1
        # body_outer = body_eff > 1 时 body_e.shift - 1（扣除 binder 引入的 1）
        ...
```

Proj（投影）较简单，只有一个子表达式：

```python
    elif "proj" in obj:
        ...
        struct_eff = 0 if struct_core_nlbv == 0 else struct_core_nlbv + struct_e.shift
        min_shift = CLOSED_SHIFT if struct_eff == 0 else struct_e.shift
        ...
```

### 辅助计算

```python
def _num_loose_bvars(self, core: int) -> int:
    return self.dag.expr_nlbv[core]

def name_to_string(self, ptr: int) -> str:
    name = self.dag.get_name(ptr)
    if name.tag == 'Anon':
        return ''
    if name.tag == 'Str':
        pfx_str = self.name_to_string(name.pfx) if name.pfx is not None else ''
        out = pfx_str + ('.' if pfx_str else '') + self.dag.strings[name.sfx]
        return out
    if name.tag == 'Num':
        ...
```

`expr_nlbv` 是 DAG 中预计算的非局部绑定变量数量，用于确定一个表达式是否需要 shift。

## 声明解析

六个 handler 分别对应七种 Declar 类型（InductiveDecl 同时产生 ConstructorDecl 和 RecursorDecl）。

### Axiom

```python
def _handle_axiom(self, data: dict):
    name = self.get_name_ptr(data["name"])
    uparams = self.get_uparams_ptr(data.get("levelParams", []))
    ty = self.get_core_ptr(data["type"])
    is_unsafe = data.get("isUnsafe", False)
    info = DeclarInfo(name=name, uparams=uparams, ty=ty)
    decl = Axiom(info=info, is_unsafe=is_unsafe)
    if self.config.unsafe_permit_all_axioms or (
        self.config.permitted_axioms is not None
        and self.name_to_string(name) in self.config.permitted_axioms
    ):
        assert name not in self.declars
        self.declars[name] = decl
    else:
        if self.config.unpermitted_axiom_hard_error:
            raise ValueError(...)
        else:
            self.skipped.append(name_string)
```

公理有两种控制策略：
- **白名单模式**：`permitted_axioms` 列表中有名字才接受
- **全放开模式**：`unsafe_permit_all_axioms` 接受所有
- **软失败模式**：`unpermitted_axiom_hard_error = false` 时跳过而非报错

### Theorem / Definition / Opaque

三者结构相同，差别只在元数据：

```python
def _handle_thm(self, data: dict):
    name = self.get_name_ptr(data["name"])
    uparams = self.get_uparams_ptr(data.get("levelParams", []))
    ty = self.get_core_ptr(data["type"])
    val = self.get_core_ptr(data["value"])
    info = DeclarInfo(name=name, uparams=uparams, ty=ty)
    decl = Theorem(info=info, value=val)
    assert name not in self.declars
    self.declars[name] = decl

def _handle_def(self, data: dict):
    ...
    hint = self._parse_reducibility_hint(data["hints"])
    safety = data.get("safety", "safe")
    decl = Definition(info=info, value=val, hint=hint, safety=safety)
    ...

def _handle_opaque(self, data: dict):
    ...
    is_unsafe = data.get("isUnsafe", False)
    decl = OpaqueDecl(info=info, value=val, is_unsafe=is_unsafe)
    ...
```

Definition 多出 `hints`（reducibility hint）和 `safety` 字段：

```python
def _parse_reducibility_hint(self, hints_val) -> ReducibilityHint:
    if hints_val == "opaque":
        return Opaque()
    if hints_val == "abbrev":
        return Abbrev()
    if isinstance(hints_val, dict) and "regular" in hints_val:
        return Regular(hints_val["regular"])
    if hints_val == "regular":
        return Regular(0)
    raise ValueError(f"Unknown reducibility hint: {hints_val}")
```

Reducibility hint 控制 δ 归约的行为：`Opaque` 不展开，`Abbrev` 始终展开，`Regular(n)` 按展开次数排序（用于 DefEq 的 Lazy Delta）。

### Inductive

`_handle_inductive` 是最长的 handler（约 100 行），因为它要同时构造三种 Declar：

```python
def _handle_inductive(self, data: dict):
    ind_vals = data.get("types", [])
    ctor_vals = data.get("ctors", [])
    rec_vals = data.get("recs", [])

    # 1. 解析所有归纳类型的元数据
    all_inductive_data = []
    for ind_info in ind_vals:
        ...  # 构造 InductiveData（含 uparams, ty, all_ctor_names, num_params 等）

    # 2. 解析所有构造器的元数据
    all_constructor_data = []
    for ctor_info in ctor_vals:
        ...  # 构造 ConstructorData（含 cidx, num_fields, parent_inductive 等）

    # 3. 解析所有消去子的元数据
    all_recursor_data = []
    for rec_info in rec_vals:
        ...  # 构造 RecursorData（含 num_motives, num_minors, rules 等）

    # 4. 为每个归纳类型创建 InductiveDecl
    for ind_data in all_inductive_data:
        decl = InductiveDecl(info=ind_data.info,
            inductives=all_inductive_data,
            constructors=all_constructor_data,
            recursors=all_recursor_data)
        self.declars[ind_data.info.name] = decl

    # 5. 为每个构造器创建 ConstructorDecl
    for ctor_data in all_constructor_data:
        decl = ConstructorDecl(info=ctor_data.info, data=ctor_data)
        self.declars[ctor_data.info.name] = decl

    # 6. 为每个消去子创建 RecursorDecl
    for rec_data in all_recursor_data:
        decl = RecursorDecl(info=rec_data.info, data=rec_data)
        self.declars[rec_data.info.name] = decl
```

关键设计：每个 `InductiveDecl` 都携带**完整的互递归块信息**（所有 inductive、constructor、recursor），但每个名字也只创建一个 `InductiveDecl`。这样 `check_decl` 在处理时无论遇到块中哪个归纳类型的名字，都能拿到完整的互递归上下文。

### Quot

```python
def _handle_quot(self, data: dict):
    ...
    kind = data.get("kind", "type")
    decl = QuotDecl(info=info, kind=kind)
    self.declars[name] = decl
```

商类型，目前只做元信息记录。

## get_uparams_ptr — Universe 参数解析

```python
def get_uparams_ptr(self, name_idxs: List[int]) -> int:
    levels = []
    for name_idx in name_idxs:
        name_ptr = self.get_name_ptr(name_idx)
        param_level = Level.param(name_ptr)
        dag_idx = self.dag.level_map.get(param_level)
        if dag_idx is None:
            raise ValueError(...)
        levels.append(dag_idx)
    return self.dag.insert_uparams(tuple(levels))
```

Universe 多态参数（如 `List.{u}` 中的 `u`）被解析为 `Level.param` 并插入 DAG 的 level 表中。`insert_uparams` 将这些 level 打包成一个元组指针。

## finalize — 产出 ExportFile

```python
def finalize(self) -> ExportFile:
    return ExportFile(self.dag, self.declars, self.config, self.skipped)

def parse_export_file(file_path: str, config) -> ExportFile:
    parser = Parser(LeanDag.with_capacity(config, 0), config)
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                parser.feed_line(line)
    return parser.finalize()
```

入口函数 `parse_export_file` 完成从文件路径到 ExportFile 的全流程：创建 Parser → 逐行 feed → 产出 ExportFile。

## 关键方法一览

```python
Parser.__init__              # 初始化 remap 数组和 declars
Parser.feed_line             # 逐行主分派
Parser.finalize              # 产出 ExportFile
Parser.get_name_ptr          # 导出索引 → DAG Name 索引
Parser.get_level_ptr         # 导出索引 → DAG Level 索引
Parser.get_expr_ptr          # 导出索引 → ExprPtr (core, shift)
Parser.get_core_ptr          # 导出索引 → 闭项 core
Parser.get_levels_ptr        # 导出索引列表 → DAG Level 元组指针
Parser.get_uparams_ptr       # universe 参数名列表 → 参数 level 元组指针
Parser._handle_meta          # 版本检查
Parser._handle_name_str      # 字符串名字
Parser._handle_name_num      # 数值名字
Parser._handle_level         # 宇宙层级
Parser._handle_expr          # 表达式（含 OSNF）
Parser._handle_axiom         # 公理
Parser._handle_thm           # 定理
Parser._handle_def           # 定义
Parser._handle_opaque        # 不透明定义
Parser._handle_quot          # 商类型
Parser._handle_inductive     # 归纳类型（含构造器和消去子）
```
