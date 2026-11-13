#!/usr/bin/env python3
"""Verify this portable source bundle and replay its finite F4 certificate.

Python 3 standard library only. Run without -O. Evidence files are never changed.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    require(__debug__, "Assertions must remain enabled; do not use python -O.")
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "MANIFEST.json").read_text(encoding="utf-8"))
    require(manifest["schema"] == "f4-source-bundle-v1", "Unknown manifest schema.")
    entries = manifest["files"]
    for entry in entries:
        relative = Path(entry["path"])
        require(not relative.is_absolute() and ".." not in relative.parts,
                "Unsafe manifest path.")
        path = root / relative
        require(path.is_file() and not path.is_symlink(),
                "Missing or invalid bundle file: " + entry["path"])
        data = path.read_bytes()
        require(len(data) == entry["bytes"], "Size mismatch: " + entry["path"])
        require(hashlib.sha256(data).hexdigest() == entry["sha256"],
                "SHA-256 mismatch: " + entry["path"])
    expected_bytes = (root / "evidence/results.json").read_bytes()
    expected = json.loads(expected_bytes)
    verifier = root / "evidence/verify_f4.py"
    digest = hashlib.sha256(verifier.read_bytes()).hexdigest()
    require(expected["source_sha256"] == digest,
            "Published evidence does not belong to the bundled verifier.")
    with tempfile.TemporaryDirectory(prefix="f4_replay_") as work:
        work = Path(work)
        shutil.copyfile(verifier, work / "verify_f4.py")
        optimized = subprocess.run(
            [sys.executable, "-I", "-O", str(work / "verify_f4.py")],
            cwd=work, text=True, capture_output=True)
        require(optimized.returncode != 0 and
                "Assertions are required" in optimized.stderr and
                not (work / "results.json").exists(),
                "Optimized execution was not rejected before producing results.")
        # -I ignores PYTHON* environment overrides, including PYTHONOPTIMIZE.
        started = time.monotonic()
        run = subprocess.run([sys.executable, "-I", str(work / "verify_f4.py")],
                             cwd=work, text=True, capture_output=True)
        elapsed = round(time.monotonic() - started, 3)
        require(run.returncode == 0,
                "Finite verifier failed:\n" + run.stdout + run.stderr)
        actual_bytes = (work / "results.json").read_bytes()
        actual = json.loads(actual_bytes)
    require(actual_bytes == expected_bytes,
            "Replay result bytes differ from the published deterministic evidence.")
    require(actual["status"] == "PASS", "Verifier did not report PASS.")
    print(json.dumps({
        "bundle_integrity": "PASS",
        "verified_files": len(entries),
        "finite_replay": "PASS",
        "result_bytes_match": True,
        "optimized_mode_rejected": True,
        "verifier_sha256": digest,
        "replay_elapsed_seconds": elapsed,
        "scope": "F4-local factorized finite evidence; not all-degree or full F2 acceptance"
    }, indent=2))


if __name__ == "__main__":
    main()
