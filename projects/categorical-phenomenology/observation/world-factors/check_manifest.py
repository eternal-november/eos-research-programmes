#!/usr/bin/env python3
"""Verify every file listed in the delivered SHA-256 manifest."""
from pathlib import Path
import hashlib
import json
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / "sha256.json").read_text())
for name, expected in manifest.items():
    actual = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"SHA-256 mismatch: {name}")
print(f"Verified {len(manifest)} file hashes.")
