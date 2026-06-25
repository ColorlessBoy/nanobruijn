"""CLI entry point for Python nanobruijn: reads NDJSON from stdin (or file arg), runs checker."""
import sys
import argparse
from .dag import LeanDag
from .parser import Parser, ExportFile
from .config import Config


def main():
    parser_args = argparse.ArgumentParser()
    parser_args.add_argument("input", nargs="?", help="NDJSON export file (stdin if omitted)")
    args = parser_args.parse_args()

    cfg = Config()
    cfg.use_stdin = args.input is None
    cfg.nat_extension = True
    cfg.string_extension = True
    cfg.unpermitted_axiom_hard_error = False
    cfg.unsafe_permit_all_axioms = True

    dag = LeanDag.with_capacity(cfg, 0)
    parser = Parser(dag, cfg)

    fp = open(args.input) if args.input else sys.stdin
    for line in fp:
        line = line.strip()
        if line:
            try:
                parser.feed_line(line)
            except (ValueError, KeyError, AssertionError) as e:
                print(f"PARSE ERROR: {e}", file=sys.stderr)
                sys.exit(1)
    if args.input:
        fp.close()

    export: ExportFile = parser.finalize()
    panics = export.check_all_declars()
    if panics > 0:
        print(f"{panics} declaration(s) failed type checking", file=sys.stderr)
        sys.exit(1)

    print("Checked all declarations with no errors", file=sys.stderr)


if __name__ == "__main__":
    main()
