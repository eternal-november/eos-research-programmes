#!/usr/bin/env python3
from pathlib import Path
import sys, subprocess, tempfile
here=Path(__file__).resolve().parent
up=Path(sys.argv[1]).resolve()
base=Path(sys.argv[2]).resolve() if len(sys.argv)>2 else here.parent
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    for f in ('fixture.inc','replay.py'):(d/f).write_bytes((base/f).read_bytes())
    child=d/'dual-writer';child.mkdir()
    (child/'replay.py').write_bytes((base/'dual-writer'/'replay.py').read_bytes())
    (child/'order.inc').write_bytes((here/'split.inc').read_bytes())
    subprocess.run([sys.executable,'-B',child/'replay.py',up],check=True)
