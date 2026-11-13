#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(r/'check_tex_source.py')],cwd=r,check=True)
subprocess.run(['sh',str(r/'run_exact_checks.sh')],cwd=r,check=True)
print('PASS: retained checks and clean reproduction; TeX uncompiled')
