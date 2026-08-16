from __future__ import annotations

import json
from dataclasses import dataclass


@dataclass
class Config:
    export_file_path: str | None = None
    use_stdin: bool = False
    permitted_axioms: list[str] | None = None
    unpermitted_axiom_hard_error: bool = True
    num_threads: int = 1
    nat_extension: bool = False
    string_extension: bool = False
    pp_declars: list[str] | None = None
    unknown_pp_declar_hard_error: bool = True
    pp_output_path: str | None = None
    pp_to_stdout: bool = False
    print_success_message: bool = False
    print_axioms: bool = True
    unsafe_permit_all_axioms: bool = False
    max_declarations: int = 0
    skip_declarations: int = 0
    declaration_filter: str | None = None
    declaration_timeout_secs: int = 0
    use_nanoda_tc: bool = False

    def validate(self) -> None:
        if self.export_file_path is None and not self.use_stdin:
            raise ValueError(
                "incompatible config options: must specify a path to an export file "
                "OR set `use_stdin: true`"
            )
        if self.export_file_path is not None and self.use_stdin:
            raise ValueError(
                "incompatible config options: if an export file path is given, "
                "`use_stdin` cannot be `true`"
            )
        if self.unsafe_permit_all_axioms:
            if self.unpermitted_axiom_hard_error:
                raise ValueError(
                    "incompatible config options: unsafe_permit_all_axioms && "
                    "unpermitted_axioms_hard_error"
                )
            if self.permitted_axioms is not None and len(self.permitted_axioms) > 0:
                raise ValueError(
                    "incompatible config options: unsafe_permit_all_axioms && "
                    "nonempty permitted_axioms list"
                )

    @classmethod
    def from_json(cls, path: str) -> Config:
        with open(path, 'r') as f:
            data = json.load(f)
        valid_keys = cls.__dataclass_fields__.keys()
        config = cls(**{k: v for k, v in data.items() if k in valid_keys})
        config.validate()
        return config
