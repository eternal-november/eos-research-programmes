#!/usr/bin/env python3
"""Rerun the bundled finite regressions without modifying the source package.

Python 3 standard library only. Each script runs without Python optimization,
so its assertions are active. Results are compared as JSON values, not by
serialization whitespace. This is regression checking, not formal proof.
"""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def main():
    directory = Path(__file__).resolve().parent
    cases = json.loads((directory / "check_manifest.json").read_text())
    with tempfile.TemporaryDirectory(prefix="crossing-reconstruction-checks-") as temporary:
        work = Path(temporary)
        for source in directory.rglob("*.py"):
            target = work / source.relative_to(directory)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
        for case in cases:
            script = work / case["script"]
            completed = subprocess.run(
                [sys.executable, "-B", str(script)],
                cwd=work,
                text=True,
                capture_output=True,
                check=True,
            )
            generated = work / case["result"]
            actual = json.loads(generated.read_text() if generated.exists() else completed.stdout)
            expected = json.loads((directory / case["result"]).read_text())
            if actual != expected:
                raise RuntimeError("Bundled result differs from rerun: " + case["script"])
            print("PASS  " + case["script"], flush=True)
    print("All " + str(len(cases)) + " bundled check results reproduced.")


if __name__ == "__main__":
    main()
