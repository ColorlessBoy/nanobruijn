"""CLI entry point for Python nanobruijn: reads NDJSON from stdin, runs checker."""
import sys
from .dag import LeanDag
from .parser import Parser
from .config import Config


def main():
    cfg = Config()
    cfg.use_stdin = True
    cfg.nat_extension = True
    cfg.string_extension = True
    cfg.unpermitted_axiom_hard_error = False
    cfg.unsafe_permit_all_axioms = True

    dag = LeanDag.with_capacity(cfg, 0)
    parser = Parser(dag, cfg)

    for line in sys.stdin:
        line = line.strip()
        if line:
            try:
                parser.feed_line(line)
            except (ValueError, KeyError, AssertionError) as e:
                print(f"PARSE ERROR: {e}", file=sys.stderr)
                sys.exit(1)

    export = parser.finalize()
    panics = export.check_all_declars()
    if panics > 0:
        print(f"{panics} declaration(s) failed type checking", file=sys.stderr)
        sys.exit(1)

    print("Checked all declarations with no errors", file=sys.stderr)


if __name__ == "__main__":
    main()
