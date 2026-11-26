#!/usr/bin/env python3
import subprocess,sys,tempfile
from pathlib import Path
here=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    (d/'replay.py').write_bytes((here.parent/'replay.py').read_bytes())
    (d/'standins.inc').write_bytes((here.parent/'standins.inc').read_bytes())
    (d/'tests.inc').write_bytes((here/'scope-test.inc').read_bytes())
    subprocess.run([sys.executable,d/'replay.py',*sys.argv[1:]],check=True)
