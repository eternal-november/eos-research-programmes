#!/usr/bin/env python3
"""Run every bundled check without compiling TeX; Python standard library only."""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent
commands = [
    ['check_rig_native_cells.py'],
    ['check_capability_fixture.py'],
    ['check_probability_fixture.py'],
    ['check_group_balance.py'],
    ['check_tex_source.py', 'General_Independent_Interaction_Criterion.tex',
     '--output', 'source_integrity_results.json'],
]
results = []
for args in commands:
    result = subprocess.run([sys.executable, *args], cwd=root, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    record = {'script': args[0], 'arguments': args[1:], 'exit_code': result.returncode,
              'stdout': result.stdout, 'stderr': result.stderr}
    results.append(record)
    print(args[0] + ': ' + ('PASS' if result.returncode == 0 else 'FAIL'))
summary = {'all_passed': all(r['exit_code'] == 0 for r in results),
           'compiled_tex': False, 'proof_assistant_verified': False,
           'visual_layout_verified': False, 'checks': results}
(root/'check_results.json').write_text(json.dumps(summary, indent=2)+'\n')
raise SystemExit(0 if summary['all_passed'] else 1)
