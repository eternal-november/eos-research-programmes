#!/usr/bin/env python3
"""Project the exact native parent, overlay the locked source delta, reject extra/missing bytes."""
import hashlib
import json
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
parent, output = (Path(x).resolve() for x in sys.argv[1:])
if output.exists():
    raise SystemExit(f"refusing existing output: {output}")
basebytes = (here / "parent-source.json").read_bytes()
base = json.loads(basebytes)
final = json.loads((here / "final-source.json").read_bytes())
git = json.loads((here / "parent-git.json").read_bytes())
assert len(base) == 507
assert hashlib.sha256(basebytes).hexdigest() == "e338a0414d4aab098946a77828c51be362f53765f7ad3cb23d4e9a59e357faa8"
assert git["commit"] == "f458186590df968a516ba73a8eb76fcf044544b0"
assert git["tree"] == "1c829c869d1c15e907b1f2404cad74e6fd88f1b7"
assert set(base) <= set(final) and set(git["nativeRows"]) == set(base)
overlay = here / "overlay"
changed = {k for k, v in final.items() if v != base.get(k)}
assert changed == {str(p.relative_to(overlay)) for p in overlay.rglob("*") if p.is_file()}
for k, v in base.items():
    data = (parent / k).read_bytes()
    assert hashlib.sha256(data).hexdigest() == v, k
    assert hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest() == git["nativeRows"][k], k
for k, v in final.items():
    data = ((overlay if k in changed else parent) / k).read_bytes()
    assert hashlib.sha256(data).hexdigest() == v, k
    out = output / k
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(data)
actual = {str(p.relative_to(output)) for p in output.rglob("*") if p.is_file()}
assert actual == set(final)
print(f"PASS: {len(base)} parent paths; {len(changed)} locked overlay paths; {len(final)} final paths")
