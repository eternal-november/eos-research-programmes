#!/usr/bin/env python3
"""Reproduce the exact finite-example checks and deterministic JSON snapshot."""

import argparse
import json
from pathlib import Path
import sys

# Do not leave bytecode or other unlisted artifacts in the deliverable.
sys.dont_write_bytecode = True

from check_automata import run as run_automata
from check_posets import run as run_posets


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", type=Path, help="Write the newly computed deterministic JSON snapshot")
    mode.add_argument("--verify", type=Path, help="Compare newly computed results against an existing snapshot")
    args = parser.parse_args()

    result = {
        "status": "PASS",
        "scope": "Exact finite checks of the stated examples and bounded exhaustive families, not proofs of general theorems, model promises, or novelty.",
        "arithmetic": "Exact integers, finite sets, and tuples; no external packages or floating-point arithmetic.",
        **run_posets(),
        **run_automata(),
    }
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(rendered, encoding="utf-8")
        print("PASS: all checks completed; deterministic results written to " + str(args.write))
    elif args.verify:
        expected = args.verify.read_text(encoding="utf-8")
        if expected != rendered:
            raise RuntimeError("All assertions passed, but the result snapshot differs: " + str(args.verify))
        print("PASS: all checks completed; deterministic results exactly match " + str(args.verify))
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
