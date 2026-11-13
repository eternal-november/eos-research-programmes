#!/usr/bin/env python3
"""Reproduce exact tests without network or dependencies."""
from pathlib import Path
import subprocess, sys
root=Path(__file__).resolve().parent
expected=(root/"checks/expected_output.txt").read_bytes()
for flags in ([],["-O"]):
    result=subprocess.run([sys.executable,*flags,str(root/"checks/joint_gluing_checks.py")],cwd=root,capture_output=True)
    if result.returncode or result.stdout!=expected:
        sys.stderr.buffer.write(result.stderr)
        raise SystemExit("Exact check reproduction failed: "+str(flags))
print("All 9 exact check groups reproduced normally and with -O.")
print("TeX source is uncompiled. Checks supplement the proofs and do not establish novelty.")
