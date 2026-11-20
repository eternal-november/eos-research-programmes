#!/usr/bin/env python3
"""Run three expected-failure controls in temporary files; the source is never edited."""
import subprocess
import sys
import tempfile
from pathlib import Path

root = Path(sys.argv[1]).resolve()
runner = sys.argv[2:] or ["lean"]
src = (root / "checks/DiscreteTransposition.lean").read_text()

mutations = [
    ("identity-only pure observation", 
     "let f : Bool ⟶ Bool := TypeCat.ofHom fun _ => true",
     "let f : Bool ⟶ Bool := TypeCat.ofHom id",
     "is not definitionally equal"),
    ("exchange the two mapped projections",
     "      (false, true) := rfl",
     "      (true, false) := rfl",
     "Type mismatch"),
    ("forget fiber-product membership",
     "∀ q : MappedPullback continuationMonad.toFunctor toUnit toUnit,",
     "∀ q : { x : Cont Bool × Cont Bool // True },",
     "Application type mismatch"),
]
with tempfile.TemporaryDirectory(prefix="discrete-transposition-controls-") as directory:
    f = Path(directory) / "Control.lean"
    for label, expected, replacement, diagnostic in mutations:
        assert src.count(expected) == 1, label
        f.write_text(src.replace(expected, replacement))
        result = subprocess.run([*runner, str(f)], cwd=root, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        if result.returncode == 0 or diagnostic not in result.stdout:
            print(result.stdout.replace(str(f), f.name))
            raise SystemExit(f"unexpected mutation result: {label}")
        first = next(s for s in result.stdout.splitlines() if ": error:" in s)
        print(f"PASS rejection: {label}")
        print(first.replace(str(f), f.name))
