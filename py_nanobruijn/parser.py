from __future__ import annotations
import json
from typing import List, Tuple, Dict, Optional, TYPE_CHECKING

from .name import Name
from .level import Level
from .expr import Expr, BinderStyle
from .ptr import ExprPtr, CLOSED_SHIFT
from .dag import LeanDag
from .env import (
    Declar, Axiom, Theorem, Definition, OpaqueDecl, QuotDecl,
    InductiveDecl, ConstructorDecl, RecursorDecl,
    DeclarInfo, InductiveData, ConstructorData, RecursorData,
    RecRule, ReducibilityHint, Opaque, Regular, Abbrev, Env, EnvLimit,
)

if TYPE_CHECKING:
    from .tc_whnf import TypeChecker


class ExportFile:
    def __init__(self, dag, declars, config, skipped=None):
        self.dag = dag
        self.declars = declars
        self.config = config
        self.skipped = skipped or []

    # --- Patched by check_decl.py ---
    def check_declar(self, d) -> None: ...
    def _check_declar_shift(self, d) -> None: ...
    def _check_declar_nanoda(self, d) -> None: ...
    def check_all_declars(self) -> int: ...
    def _check_all_declars_serial(self) -> int: ...
    def _make_env(self, limit: Optional[EnvLimit] = None) -> Env: ...
    def _with_tc(self, d: Declar) -> TypeChecker: ...
    def name_to_string(self, ptr) -> str: ...

    # --- Patched by inductive.py ---
    def check_inductive_declar(self, d, declars) -> None: ...

    # --- Patched by quot.py ---
    def check_quot(self, d) -> None: ...


class Parser:
    def __init__(self, dag: LeanDag, config):
        self.dag = dag
        self.config = config
        self.declars: Dict[int, Declar] = {}
        self.skipped: List[str] = []
        self.name_remap: List[int] = [0]
        self.level_remap: List[int] = [0]
        self.expr_remap: List[Tuple[int, int]] = []
        self.osnf_count = 0

    # ---- helpers ----

    def _ensure_name_remap(self, export_idx: int):
        if export_idx >= len(self.name_remap):
            self.name_remap.extend([-1] * (export_idx + 1 - len(self.name_remap)))

    def _ensure_level_remap(self, export_idx: int):
        if export_idx >= len(self.level_remap):
            self.level_remap.extend([-1] * (export_idx + 1 - len(self.level_remap)))

    def _ensure_expr_remap(self, export_idx: int):
        if export_idx >= len(self.expr_remap):
            self.expr_remap.extend([(-1, 0)] * (export_idx + 1 - len(self.expr_remap)))

    def get_name_ptr(self, idx: int) -> int:
        dag_idx = self.name_remap[idx] if idx < len(self.name_remap) else -1
        if dag_idx == -1:
            raise ValueError(f"export references name index {idx} before it is defined")
        return dag_idx

    def get_level_ptr(self, idx: int) -> int:
        dag_idx = self.level_remap[idx] if idx < len(self.level_remap) else -1
        if dag_idx == -1:
            raise ValueError(f"export references level index {idx} before it is defined")
        return dag_idx

    def get_expr_ptr(self, idx: int) -> ExprPtr:
        if idx >= len(self.expr_remap):
            dag_idx, shift = -1, 0
        else:
            dag_idx, shift = self.expr_remap[idx]
        if dag_idx == -1:
            raise ValueError(f"export references expression index {idx} before it is defined")
        if shift == CLOSED_SHIFT:
            return ExprPtr.closed(dag_idx)
        return ExprPtr(dag_idx, shift)

    def get_core_ptr(self, idx: int) -> int:
        ep = self.get_expr_ptr(idx)
        if not ep.is_closed():
            raise ValueError(f"expected closed expression for declaration, got shift={ep.shift}")
        return ep.core

    def get_levels_ptr(self, idxs: List[int]) -> int:
        levels = tuple(self.get_level_ptr(i) for i in idxs)
        return self.dag.insert_uparams(levels)

    def get_uparams_ptr(self, name_idxs: List[int]) -> int:
        levels = []
        for name_idx in name_idxs:
            name_ptr = self.get_name_ptr(name_idx)
            param_level = Level.param(name_ptr)
            dag_idx = self.dag.level_map.get(param_level)
            if dag_idx is None:
                raise ValueError(f"Level::Param for name index {name_idx} not found")
            levels.append(dag_idx)
        return self.dag.insert_uparams(tuple(levels))

    def _num_loose_bvars(self, core: int) -> int:
        return self.dag.expr_nlbv[core]

    def _find_or_insert_var0(self) -> int:
        var0 = Expr.var(0)
        idx = self.dag.expr_map.get(var0)
        if idx is not None:
            return idx
        idx, _ = self.dag.insert_expr(var0)
        return idx

    def name_to_string(self, ptr: int) -> str:
        name = self.dag.get_name(ptr)
        if name.tag == 'Anon':
            return ''
        if name.tag == 'Str':
            pfx_str = self.name_to_string(name.pfx) if name.pfx is not None else ''
            out = pfx_str
            if out:
                out += '.'
            assert name.sfx is not None
            out += self.dag.strings[name.sfx]
            return out
        if name.tag == 'Num':
            pfx_str = self.name_to_string(name.pfx) if name.pfx is not None else ''
            out = pfx_str
            if out:
                out += '.'
            assert name.sfx is not None
            out += str(name.sfx)
            return out
        return ''

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

    # ---- handlers ----

    def _handle_meta(self, meta: dict):
        format_ver = meta.get("format", {}).get("version", "0.0.0")
        parts = format_ver.split(".")
        major, minor, _ = int(parts[0]), int(parts[1]), int(parts[2])
        if major < 3 or (major == 3 and minor < 1):
            raise ValueError(
                f"export format version is less than the minimum supported version. "
                f"Found {format_ver}, but min supported is 3.1.0"
            )
        if major > 3 or (major == 3 and minor >= 2):
            raise ValueError(
                f"export format version is greater than the maximum supported version. "
                f"Found {format_ver}, but max (exclusive) supported is 3.2.0"
            )

    def _handle_name_str(self, obj: dict):
        export_idx = obj["in"]
        pre = obj["str"]["pre"]
        s = obj["str"]["str"]
        pfx = self.get_name_ptr(pre)
        sfx = self.dag.insert_string(s)
        dag_idx = self.dag.insert_name(Name.str(pfx, sfx))
        self._ensure_name_remap(export_idx)
        self.name_remap[export_idx] = dag_idx

    def _handle_name_num(self, obj: dict):
        export_idx = obj["in"]
        pre = obj["num"]["pre"]
        i = obj["num"]["i"]
        pfx = self.get_name_ptr(pre)
        dag_idx = self.dag.insert_name(Name.num(pfx, i))
        self._ensure_name_remap(export_idx)
        self.name_remap[export_idx] = dag_idx

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
        self._ensure_level_remap(export_idx)
        self.level_remap[export_idx] = dag_idx

    def _handle_expr(self, obj: dict):
        export_idx = obj["ie"]

        if "sort" in obj:
            level = self.get_level_ptr(obj["sort"])
            dag_idx, _ = self.dag.insert_expr(Expr.sort(level))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)

        elif "bvar" in obj:
            dbj_idx = obj["bvar"]
            var0_idx = self._find_or_insert_var0()
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (var0_idx, dbj_idx)

        elif "const" in obj:
            c = obj["const"]
            name = self.get_name_ptr(c["name"])
            levels = self.get_levels_ptr(c.get("us", []))
            dag_idx, _ = self.dag.insert_expr(Expr.const(name, levels))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)

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
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, min_shift)

        elif "forallE" in obj:
            pi = obj["forallE"]
            binder_name = self.get_name_ptr(pi["name"])
            binder_info = BinderStyle(pi["binderInfo"])
            ty_e = self.get_expr_ptr(pi["type"])
            body_e = self.get_expr_ptr(pi["body"])
            ty_core_nlbv = self._num_loose_bvars(ty_e.core)
            body_core_nlbv = self._num_loose_bvars(body_e.core)
            ty_eff = 0 if ty_core_nlbv == 0 else ty_core_nlbv + ty_e.shift
            body_eff = 0 if body_core_nlbv == 0 else body_core_nlbv + body_e.shift
            body_outer = None if body_eff <= 1 else body_e.shift - 1
            if ty_eff == 0 and body_outer is None:
                min_shift = CLOSED_SHIFT
            elif ty_eff > 0 and body_outer is None:
                min_shift = ty_e.shift
            elif ty_eff == 0 and body_outer is not None:
                min_shift = body_outer
            else:
                assert body_outer is not None
                min_shift = min(ty_e.shift, body_outer)
            if 0 < min_shift < CLOSED_SHIFT:
                self.osnf_count += 1
            core_ty = ty_e if ty_eff == 0 else ExprPtr(ty_e.core, ty_e.shift - min_shift)
            core_body = body_e if body_eff <= 1 else ExprPtr(body_e.core, body_e.shift - min_shift)
            dag_idx, _ = self.dag.insert_expr(Expr.pi(binder_name, binder_info, core_ty, core_body))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, min_shift)

        elif "lam" in obj:
            lm = obj["lam"]
            binder_name = self.get_name_ptr(lm["name"])
            binder_info = BinderStyle(lm["binderInfo"])
            ty_e = self.get_expr_ptr(lm["type"])
            body_e = self.get_expr_ptr(lm["body"])
            ty_core_nlbv = self._num_loose_bvars(ty_e.core)
            body_core_nlbv = self._num_loose_bvars(body_e.core)
            ty_eff = 0 if ty_core_nlbv == 0 else ty_core_nlbv + ty_e.shift
            body_eff = 0 if body_core_nlbv == 0 else body_core_nlbv + body_e.shift
            body_outer = None if body_eff <= 1 else body_e.shift - 1
            if ty_eff == 0 and body_outer is None:
                min_shift = CLOSED_SHIFT
            elif ty_eff > 0 and body_outer is None:
                min_shift = ty_e.shift
            elif ty_eff == 0 and body_outer is not None:
                min_shift = body_outer
            else:
                assert body_outer is not None
                min_shift = min(ty_e.shift, body_outer)
            if 0 < min_shift < CLOSED_SHIFT:
                self.osnf_count += 1
            core_ty = ty_e if ty_eff == 0 else ExprPtr(ty_e.core, ty_e.shift - min_shift)
            core_body = body_e if body_eff <= 1 else ExprPtr(body_e.core, body_e.shift - min_shift)
            dag_idx, _ = self.dag.insert_expr(Expr.lambda_(binder_name, binder_info, core_ty, core_body))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, min_shift)

        elif "letE" in obj:
            lt = obj["letE"]
            binder_name = self.get_name_ptr(lt["name"])
            ty_e = self.get_expr_ptr(lt["type"])
            val_e = self.get_expr_ptr(lt["value"])
            body_e = self.get_expr_ptr(lt["body"])
            nondep = lt.get("nondep", False)
            ty_core_nlbv = self._num_loose_bvars(ty_e.core)
            val_core_nlbv = self._num_loose_bvars(val_e.core)
            body_core_nlbv = self._num_loose_bvars(body_e.core)
            ty_eff = 0 if ty_core_nlbv == 0 else ty_core_nlbv + ty_e.shift
            val_eff = 0 if val_core_nlbv == 0 else val_core_nlbv + val_e.shift
            body_eff = 0 if body_core_nlbv == 0 else body_core_nlbv + body_e.shift
            body_outer = None if body_eff <= 1 else body_e.shift - 1
            min_shift = CLOSED_SHIFT
            if ty_eff > 0:
                min_shift = min(min_shift, ty_e.shift)
            if val_eff > 0:
                min_shift = min(min_shift, val_e.shift)
            if body_outer is not None:
                min_shift = min(min_shift, body_outer)
            if min_shift == CLOSED_SHIFT:
                min_shift = CLOSED_SHIFT
            if 0 < min_shift < CLOSED_SHIFT:
                self.osnf_count += 1
            core_ty = ty_e if ty_eff == 0 else ExprPtr(ty_e.core, ty_e.shift - min_shift)
            core_val = val_e if val_eff == 0 else ExprPtr(val_e.core, val_e.shift - min_shift)
            core_body = body_e if body_eff <= 1 else ExprPtr(body_e.core, body_e.shift - min_shift)
            dag_idx, _ = self.dag.insert_expr(Expr.let_(binder_name, core_ty, core_val, core_body, nondep))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, min_shift)

        elif "proj" in obj:
            pr = obj["proj"]
            ty_name = self.get_name_ptr(pr["typeName"])
            idx = pr["idx"]
            struct_e = self.get_expr_ptr(pr["struct"])
            struct_core_nlbv = self._num_loose_bvars(struct_e.core)
            struct_eff = 0 if struct_core_nlbv == 0 else struct_core_nlbv + struct_e.shift
            min_shift = CLOSED_SHIFT if struct_eff == 0 else struct_e.shift
            if 0 < min_shift < CLOSED_SHIFT:
                self.osnf_count += 1
            core_struct = struct_e if struct_eff == 0 else ExprPtr(struct_e.core, struct_e.shift - min_shift)
            dag_idx, _ = self.dag.insert_expr(Expr.proj(ty_name, idx, core_struct))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, min_shift)

        elif "strVal" in obj:
            if not self.config.string_extension:
                raise ValueError(
                    "String lit extension disallowed by checker execution config, "
                    "but export file contains a string literal"
                )
            s = obj["strVal"]
            string_ptr = self.dag.insert_string(s)
            dag_idx, _ = self.dag.insert_expr(Expr.string_lit(string_ptr))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)

        elif "natVal" in obj:
            if not self.config.nat_extension:
                raise ValueError(
                    "Nat lit extension disallowed by checker execution config, "
                    "but export file contains a nat literal"
                )
            n = int(obj["natVal"])
            bigint_ptr = self.dag.insert_bignum(n)
            dag_idx, _ = self.dag.insert_expr(Expr.nat_lit(bigint_ptr))
            self._ensure_expr_remap(export_idx)
            self.expr_remap[export_idx] = (dag_idx, CLOSED_SHIFT)

        elif "mdata" in obj:
            raise ValueError("Expr.mdata not supported")

        else:
            raise ValueError(f"Unknown expression variant: {list(obj.keys())}")

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
            assert name not in self.declars, f"duplicate axiom declaration for {name}"
            self.declars[name] = decl
        else:
            name_string = self.name_to_string(name)
            if self.config.unpermitted_axiom_hard_error:
                raise ValueError(f"export file declares unpermitted axiom {name_string!r}")
            else:
                self.skipped.append(name_string)

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
        name = self.get_name_ptr(data["name"])
        uparams = self.get_uparams_ptr(data.get("levelParams", []))
        ty = self.get_core_ptr(data["type"])
        val = self.get_core_ptr(data["value"])
        hint = self._parse_reducibility_hint(data["hints"])
        safety = data.get("safety", "safe")
        info = DeclarInfo(name=name, uparams=uparams, ty=ty)
        decl = Definition(info=info, value=val, hint=hint, safety=safety)
        assert name not in self.declars
        self.declars[name] = decl

    def _handle_opaque(self, data: dict):
        name = self.get_name_ptr(data["name"])
        uparams = self.get_uparams_ptr(data.get("levelParams", []))
        ty = self.get_core_ptr(data["type"])
        val = self.get_core_ptr(data["value"])
        is_unsafe = data.get("isUnsafe", False)
        info = DeclarInfo(name=name, uparams=uparams, ty=ty)
        decl = OpaqueDecl(info=info, value=val, is_unsafe=is_unsafe)
        assert name not in self.declars
        self.declars[name] = decl

    def _handle_quot(self, data: dict):
        name = self.get_name_ptr(data["name"])
        uparams = self.get_uparams_ptr(data.get("levelParams", []))
        ty = self.get_core_ptr(data["type"])
        kind = data.get("kind", "type")
        info = DeclarInfo(name=name, uparams=uparams, ty=ty)
        decl = QuotDecl(info=info, kind=kind)
        assert name not in self.declars
        self.declars[name] = decl

    def _handle_inductive(self, data: dict):
        ind_vals = data.get("types", [])
        ctor_vals = data.get("ctors", [])
        rec_vals = data.get("recs", [])

        all_inductive_data = []
        for ind_info in ind_vals:
            name = self.get_name_ptr(ind_info["name"])
            uparams = self.get_uparams_ptr(ind_info.get("levelParams", []))
            ty = self.get_core_ptr(ind_info["type"])
            info = DeclarInfo(name=name, uparams=uparams, ty=ty)
            all_ctor_names = tuple(
                self.get_name_ptr(c) for c in ind_info.get("ctors", [])
            )
            all_ind_names = tuple(
                self.get_name_ptr(a) for a in ind_info.get("all", [])
            )
            ind_data = InductiveData(
                info=info,
                all_ctor_names=all_ctor_names,
                all_inductive_infos=all_ind_names,
                num_params=ind_info.get("numParams", 0),
                num_indices=ind_info.get("numIndices", 0),
                num_nested=ind_info.get("numNested", 0),
                is_rec=ind_info.get("isRec", False),
                is_reflexive=ind_info.get("isReflexive", False),
            )
            all_inductive_data.append(ind_data)

        all_constructor_data = []
        for ctor_info in ctor_vals:
            name = self.get_name_ptr(ctor_info["name"])
            uparams = self.get_uparams_ptr(ctor_info.get("levelParams", []))
            ty = self.get_core_ptr(ctor_info["type"])
            info = DeclarInfo(name=name, uparams=uparams, ty=ty)
            parent_inductive = self.get_name_ptr(ctor_info["induct"])
            ctor_data = ConstructorData(
                info=info,
                cidx=ctor_info.get("cidx", 0),
                num_params=ctor_info.get("numParams", 0),
                num_fields=ctor_info.get("numFields", 0),
                inductive_name=parent_inductive,
                inductive_names=tuple(
                    self.get_name_ptr(a) for a in ind_vals[0].get("all", [])
                ) if ind_vals else (),
            )
            all_constructor_data.append(ctor_data)

        all_recursor_data = []
        for rec_info in rec_vals:
            name = self.get_name_ptr(rec_info["name"])
            uparams = self.get_uparams_ptr(rec_info.get("levelParams", []))
            ty = self.get_core_ptr(rec_info["type"])
            info = DeclarInfo(name=name, uparams=uparams, ty=ty)
            rules = []
            for rule in rec_info.get("rules", []):
                rule_obj = RecRule(
                    ctor_name=self.get_name_ptr(rule["ctor"]),
                    ctor_telescope_size_wo_params=rule.get("nfields", 0),
                    val=self.get_core_ptr(rule["rhs"]),
                )
                rules.append(rule_obj)
            all_inductives = tuple(
                self.get_name_ptr(a) for a in rec_info.get("all", [])
            )
            rec_data = RecursorData(
                info=info,
                num_params=rec_info.get("numParams", 0),
                num_indices=rec_info.get("numIndices", 0),
                num_motives=rec_info.get("numMotives", 0),
                num_minors=rec_info.get("numMinors", 0),
                rules=tuple(rules),
                all_inductives=all_inductives,
                k=rec_info.get("k", False),
            )
            all_recursor_data.append(rec_data)

        for ind_data in all_inductive_data:
            name = ind_data.info.name
            decl = InductiveDecl(
                info=ind_data.info,
                inductives=tuple(all_inductive_data),
                constructors=tuple(all_constructor_data),
                recursors=tuple(all_recursor_data),
            )
            assert name not in self.declars
            self.declars[name] = decl

        for ctor_data in all_constructor_data:
            name = ctor_data.info.name
            decl = ConstructorDecl(info=ctor_data.info, data=ctor_data)
            assert name not in self.declars
            self.declars[name] = decl

        for rec_data in all_recursor_data:
            name = rec_data.info.name
            decl = RecursorDecl(info=rec_data.info, data=rec_data)
            assert name not in self.declars
            self.declars[name] = decl

    # ---- main ----

    def feed_line(self, line: str):
        obj = json.loads(line)
        if "meta" in obj:
            self._handle_meta(obj["meta"])
        elif "in" in obj:
            inner = obj.get("str")
            if inner is not None:
                self._handle_name_str(obj)
            elif obj.get("num") is not None:
                self._handle_name_num(obj)
            else:
                raise ValueError(f"Unknown name entry: {obj}")
        elif "il" in obj:
            self._handle_level(obj)
        elif "ie" in obj:
            self._handle_expr(obj)
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
