#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(r/'check_source.py')],cwd=r,check=True)
print('PASS: retained static source checks. TeX uncompiled; proposed results remain open.')
