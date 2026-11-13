#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parent
for args in (['check_source.py'],['check_learning_control.py'],['-O','check_learning_control.py']):
 subprocess.run([sys.executable,*args],cwd=r,check=True,stdout=subprocess.DEVNULL)
print('PASS: retained static source and exact elementary checks in normal and optimized modes.')
print('The source is uncompiled; research targets remain open and the contract is not adopted.')
