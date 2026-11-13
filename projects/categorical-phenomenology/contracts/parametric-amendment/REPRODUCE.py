#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parent
for args in (['check_source.py'],['check_learning_control.py'],['-O','check_learning_control.py']):
 subprocess.run([sys.executable,*args],cwd=r,check=True,stdout=subprocess.DEVNULL)
print('PASS: static source checks and elementary algebra in normal and optimized modes. Archive amendment replay is not performed.')
print('TeX uncompiled; proposed bridge remains open and contract unadopted.')
