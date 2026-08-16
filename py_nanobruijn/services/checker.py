"""Declaration-checking orchestration, isolated from parsing and CLI output."""
from __future__ import annotations

import time
from typing import TYPE_CHECKING

from ..env import (
    Axiom,
    ConstructorDecl,
    Declar,
    Definition,
    Env,
    EnvLimit,
    InductiveDecl,
    OpaqueDecl,
    QuotDecl,
    RecursorDecl,
    Theorem,
)
from ..inductive import check_inductive_declaration
from ..ptr import ExprPtr
from ..quot import check_quot_declaration
from ..results import CheckResult, Diagnostic
from ..tc_whnf import TypeChecker

if TYPE_CHECKING:
    from ..parser import ExportFile


class CheckerService:
    """Checks declarations from one export and returns structured diagnostics."""

    def __init__(self, export: ExportFile):
        self.export = export

    def make_type_checker(self, declaration: Declar) -> TypeChecker:
        from ..dag import TcCtx

        ctx = TcCtx(self.export.dag)
        ctx.export_file = self.export
        env = Env(self.export.declars, limit=EnvLimit("by_name", declaration.info.name))
        return TypeChecker(ctx, env, declar_info=declaration.info)

    def check_declaration(self, declaration: Declar) -> None:
        if isinstance(declaration, Axiom):
            self.make_type_checker(declaration).check_declar_info(declaration)
        elif isinstance(declaration, (Definition, Theorem, OpaqueDecl)):
            tc = self.make_type_checker(declaration)
            tc.check_declar_info(declaration)
            inferred_type = tc.infer(ExprPtr.closed(declaration.value), "check")
            tc.assert_def_eq(inferred_type, ExprPtr.closed(declaration.info.ty))
        elif isinstance(declaration, InductiveDecl):
            check_inductive_declaration(self.export, declaration, self.export.declars)
        elif isinstance(declaration, QuotDecl):
            check_quot_declaration(self.export, declaration)
        elif isinstance(declaration, ConstructorDecl):
            self.make_type_checker(declaration).check_declar_info(declaration)
            if declaration.data.inductive_name not in self.export.declars:
                raise ValueError("inductive declaration not found for constructor")
        elif isinstance(declaration, RecursorDecl):
            self.make_type_checker(declaration).check_declar_info(declaration)
            for inductive_name in declaration.data.all_inductives:
                if inductive_name not in self.export.declars:
                    raise ValueError("inductive declaration not found for recursor")

    def check_all(self, *, keep_going: bool = False) -> CheckResult:
        config = self.export.config
        started = time.monotonic()
        diagnostics: list[Diagnostic] = []
        checked = skipped = 0

        for index, declaration in enumerate(self.export.declars.values()):
            if config.max_declarations > 0 and index >= config.max_declarations:
                break
            if index < config.skip_declarations:
                skipped += 1
                continue
            name = self.export.name_to_string(declaration.info.name)
            if config.declaration_filter and config.declaration_filter not in name:
                skipped += 1
                continue
            try:
                self.check_declaration(declaration)
                checked += 1
            except Exception as error:
                diagnostics.append(Diagnostic(
                    severity="error",
                    message=str(error),
                    declaration=name,
                    declaration_index=index,
                    exception_type=type(error).__name__,
                ))
                if not keep_going:
                    raise

        elapsed_ms = int((time.monotonic() - started) * 1000)
        return CheckResult(
            checked=checked,
            failed=len(diagnostics),
            skipped=skipped,
            elapsed_ms=elapsed_ms,
            diagnostics=tuple(diagnostics),
        )
