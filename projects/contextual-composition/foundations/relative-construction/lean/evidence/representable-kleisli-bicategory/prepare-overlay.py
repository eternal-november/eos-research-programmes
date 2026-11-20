"""Build a checkout-freeze copy with exactly the added frozen inputs."""
import hashlib, json, shutil, sys
from pathlib import Path

here = Path(__file__).resolve().parent / "freeze"
candidate, out = map(Path, sys.argv[1:])
assert not out.exists()
parent = json.loads((here / "parent.json").read_bytes())
final = json.loads((here / "final-source.json").read_bytes())
assert len(parent) == 427 and len(final) == 468 and set(parent) <= set(final)
shutil.copytree(here, out)
for path in sorted(final.keys() - parent.keys()):
    data = (candidate / path).read_bytes()
    assert hashlib.sha256(data).hexdigest() == final[path], path
    dest = out / "overlay" / path
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
