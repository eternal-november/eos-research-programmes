"""Replay finite suites and compare their complete outputs; not a proof check."""
from pathlib import Path
import subprocess
import sys
root = Path(__file__).resolve().parent
for script, expected in [("verify_finite_composition.py", "expected_composition_output.txt"), ("verify_recovery_examples.py", "expected_recovery_output.txt")]:
    run = subprocess.run([sys.executable, str(root / "tests" / script)], cwd=root, capture_output=True, text=True, check=True)
    if run.stderr or run.stdout != (root / "tests" / expected).read_text():
        raise SystemExit(f"Output mismatch: {script}")
print("Both finite suites match their expected outputs.")
