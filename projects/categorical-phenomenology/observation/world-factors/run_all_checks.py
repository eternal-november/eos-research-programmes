#!/usr/bin/env python3
"""Replay every finite check with the current Python interpreter."""
from pathlib import Path
import subprocess
import sys
HERE = Path(__file__).resolve().parent
for name in ("world_checks.py", "world_code_checks.py", "world_code_exhaustive.py", "world_code_review_checks.py"):
    print(f"Running {name}", flush=True)
    subprocess.run([sys.executable, str(HERE / name)], cwd=HERE, check=True)
print("All four verification scripts passed.")
