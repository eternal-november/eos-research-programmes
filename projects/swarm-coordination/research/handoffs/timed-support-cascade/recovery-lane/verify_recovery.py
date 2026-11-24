"""Check a recovery workload without adding derived traces to the checkout."""
from pathlib import Path
from shutil import copytree
from subprocess import check_call
import sys
from tempfile import TemporaryDirectory

with TemporaryDirectory() as scratch:
    here = Path(__file__).resolve().parent
    work = Path(scratch) / "recovery-lane"
    copytree(here, work)
    for module, filename in (("replay.py", "results.json"), ("boundary.py", "boundary.json")):
        target = work / filename
        expected = target.read_bytes() if target.exists() else None
        with target.open("wb") as stream:
            check_call([sys.executable, "-B", module], cwd=work, stdout=stream)
        if expected is not None and target.read_bytes() != expected:
            raise RuntimeError(f"{filename}: replay output changed")
    for manifest in ("SHA256SUMS","FREEZE.SHA256"):
        check_call(["sha256sum","-c",manifest], cwd=work)
