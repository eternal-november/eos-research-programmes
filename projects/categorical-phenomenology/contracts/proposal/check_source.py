#!/usr/bin/env python3
"""Static TeX source QA only. Does not compile or certify layout/mathematics."""
from pathlib import Path
import hashlib, json, re
p=Path(__file__).with_name('proposal.tex')
s=p.read_text()
# Remove ordinary TeX comments, retaining escaped percent signs.
t='\n'.join(re.split(r'(?<!\\)%', line)[0] for line in s.splitlines())
errors=[]
stack=[]
for match in re.finditer(r'(?<!\\)[{}]', t):
    if match.group()=='{': stack.append(match.start())
    elif stack: stack.pop()
    else: errors.append(f'Unmatched closing brace at {match.start()}')
if stack: errors.append(f'{len(stack)} unmatched opening braces')
envs=[]
for match in re.finditer(r'\\(begin|end)\{([^}]+)\}', t):
    kind,name=match.groups()
    if kind=='begin': envs.append(name)
    elif not envs or envs[-1]!=name: errors.append(f'Environment mismatch at {name}')
    else: envs.pop()
if envs: errors.append(f'Unclosed environments: {envs}')
labels=re.findall(r'\\label\{([^}]+)\}',t)
refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',t)
keys=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',t)
cites=[k.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',t) for k in group.split(',')]
for name,items in [('label',labels),('bibliography key',keys)]:
    duplicates=sorted({x for x in items if items.count(x)>1})
    if duplicates: errors.append(f'Duplicate {name}s: {duplicates}')
if set(refs)-set(labels): errors.append(f'Unresolved refs: {sorted(set(refs)-set(labels))}')
if set(cites)-set(keys): errors.append(f'Unresolved citations: {sorted(set(cites)-set(keys))}')
if re.search(r'\\(?:input|include|includegraphics)\b',t): errors.append('Unexpected external TeX dependency')
result={'file':'proposal.tex','sha256':hashlib.sha256(s.encode()).hexdigest(),'lines':len(s.splitlines()),'words_whitespace':len(s.split()),'labels':len(labels),'references':len(refs),'bibliography_entries':len(keys),'cited_keys':len(set(cites)),'errors':errors,'status':'pass' if not errors else 'fail','scope':'Static source checks only; no compilation or rendering.'}
Path(__file__).with_name('source_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
