#!/usr/bin/env python3
"""Recompute the bridge examples with exact standard-library arithmetic."""

import argparse
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from check_threshold import run as threshold_checks
from check_incidence import run as incidence_checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--write", type=Path)
    output.add_argument("--verify", type=Path)
    args = parser.parse_args()
    results = {
        "status": "PASS",
        "scope": "Exact checks of explicit finite examples and bounded exhaustive families. Not proofs of general claims, empirical model promises, or novelty.",
        "representation": "Finite tuples and integer bit masks; zero-based row indices in logs; paper's one-based threshold labels retained.",
        "query_accounting": "Threshold counts include only added primitive calls with j=2,...,n. The old threshold table and state bound are supplied. Permutation examples count distinct reset words and every executed intervention letter.",
        **threshold_checks(),
        **incidence_checks(),
    }
    rendered = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.write:
        args.write.write_text(rendered, encoding="utf-8")
        print("PASS: wrote deterministic results to " + str(args.write))
    elif args.verify:
        if args.verify.read_text(encoding="utf-8") != rendered:
            raise RuntimeError("All checks passed, but the deterministic snapshot differs: " + str(args.verify))
        print("PASS: all checks pass and exactly match " + str(args.verify))
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
