"""Command-line interface for checking and inspecting Lean NDJSON exports."""
from __future__ import annotations

import argparse
import json
import sys

from .api import load_export
from .config import Config


def _default_config(input_path: str) -> Config:
    return Config(
        export_file_path=input_path,
        nat_extension=True,
        string_extension=True,
        unpermitted_axiom_hard_error=False,
        unsafe_permit_all_axioms=True,
    )


def _add_check_options(command: argparse.ArgumentParser) -> None:
    command.add_argument("input", help="NDJSON export file")
    command.add_argument("--declaration", help="only check declarations whose name contains this text")
    command.add_argument("--max-declarations", type=int, default=0)
    command.add_argument("--keep-going", action="store_true", help="report all failures instead of stopping at the first")
    command.add_argument("--timeout", type=float, default=0.0,
                         help="abort a declaration check after this many seconds (0 = no timeout)")
    command.add_argument("--json", action="store_true", help="write a machine-readable result to stdout")


def _run_check(args: argparse.Namespace) -> int:
    config = _default_config(args.input)
    config.declaration_filter = args.declaration
    config.max_declarations = args.max_declarations
    config.declaration_timeout_secs = args.timeout
    export = load_export(args.input, config)
    try:
        result = export.check_all(keep_going=args.keep_going)
    except Exception as error:  # noqa: BLE001 - CLI top-level catch: surface any failure as exit 1
        print(f"CHECK ERROR: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result.to_dict(), ensure_ascii=False))
    else:
        print(
            f"checked={result.checked} failed={result.failed} "
            f"skipped={result.skipped} elapsed_ms={result.elapsed_ms}",
            file=sys.stderr,
        )
        for diagnostic in result.diagnostics:
            print(f"ERROR {diagnostic.declaration}: {diagnostic.message}", file=sys.stderr)
    return 0 if result.ok else 1


def _run_inspect(args: argparse.Namespace) -> int:
    export = load_export(args.input, _default_config(args.input))
    declarations = [
        {"name": export.name_to_string(d.info.name), "kind": type(d).__name__}
        for d in export.declars.values()
    ]
    if args.declaration:
        declarations = [d for d in declarations if args.declaration in d["name"]]
    result = {"declarations": len(declarations), "skipped_records": len(export.skipped), "items": declarations}
    if args.json:
        print(json.dumps(result, ensure_ascii=False))
    else:
        print(f"declarations={result['declarations']} skipped_records={result['skipped_records']}")
        for declaration in declarations:
            print(f"{declaration['kind']}: {declaration['name']}")
    return 0


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    # Preserve the original ``python -m py_nanobruijn FILE`` invocation.
    if argv and argv[0] not in {"check", "inspect", "-h", "--help"}:
        argv.insert(0, "check")
    parser = argparse.ArgumentParser(prog="py-nanobruijn")
    subcommands = parser.add_subparsers(dest="command")
    check = subcommands.add_parser("check", help="type-check an NDJSON export")
    _add_check_options(check)
    inspect = subcommands.add_parser("inspect", help="list declarations in an NDJSON export")
    inspect.add_argument("input", help="NDJSON export file")
    inspect.add_argument("--declaration", help="only list matching declarations")
    inspect.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    if args.command is None:
        parser.print_help()
        return 2
    return _run_check(args) if args.command == "check" else _run_inspect(args)


if __name__ == "__main__":
    raise SystemExit(main())
