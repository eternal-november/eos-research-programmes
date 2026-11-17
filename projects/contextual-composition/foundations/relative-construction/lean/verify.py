#!/usr/bin/env python3
"""Replay the package and named-theorem axiom audit. No dependency installation."""
from pathlib import Path
import subprocess, re, json, hashlib
p=Path(__file__).resolve().parent
e=p/'evidence'; e.mkdir(exist_ok=True)
for f in [*p.glob('ContextualComposition/*.lean'),p/'ContextualComposition.lean']:
    text=f.read_text()
    if re.search(r'\b(sorry|admit|axiom|unsafe)\b',text):
        raise SystemExit('Forbidden proof/trust token in '+str(f))
for name,cmd in [('build',['lake','build']),('axioms',['lake','env','lean','AxiomAudit.lean'])]:
    r=subprocess.run(cmd,cwd=p,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (e/(name+'.log')).write_text(r.stdout)
    if r.returncode: raise SystemExit(r.stdout)
rows=json.loads((p/'TheoremIndex.json').read_text())
a=(e/'axioms.log').read_text()
for row in rows:
    if "'"+row['declaration']+"'" not in a: raise SystemExit('Missing theorem audit')
for axioms in re.findall(r'depends on axioms: \[([^]]*)\]',a):
    if set(axioms.split(', '))-{'propext','Quot.sound','Classical.choice'}:
        raise SystemExit('Unexpected axiom: '+axioms)
files=[*p.glob('*.lean'),*p.glob('ContextualComposition/*.lean'),p/'lean-toolchain',p/'lakefile.toml',p/'lake-manifest.json']
(e/'source_hashes.json').write_text(json.dumps({str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files},indent=2)+'\n')
print('PASS: package build and '+str(len(rows))+' named theorem axiom audits')
