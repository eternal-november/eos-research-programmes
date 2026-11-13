#!/usr/bin/env python3
"""Reproduce from a fresh temporary directory, ordinary and optimized Python."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
root=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix='native-common-clean-') as directory:
    dest=Path(directory)
    for name in ('verify.py','expected_results.json'):
        shutil.copy2(root/name,dest/name)
    normal=subprocess.run([sys.executable,'verify.py'],cwd=dest,capture_output=True,text=True,check=True)
    optimized=subprocess.run([sys.executable,'-O','verify.py'],cwd=dest,capture_output=True,text=True,check=True)
    if normal.stdout!=optimized.stdout: raise RuntimeError('normal and optimized results differ')
    if normal.stderr or optimized.stderr: raise RuntimeError('unexpected standard error')
    print(json.dumps({'normal':'passed','optimized':'passed','clean_copy':'passed','results':json.loads(normal.stdout),'sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(root.iterdir()) if p.is_file() and p.name in ('verify.py','expected_results.json','reproduce.py','README.md')}},indent=2,sort_keys=True))
