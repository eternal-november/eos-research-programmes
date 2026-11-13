#!/usr/bin/env python3
"""Static checks only: does not compile or certify rendered page layout."""
import hashlib, json, re
from pathlib import Path
ROOT = Path(__file__).resolve().parent
p=ROOT/'theory_guide.tex'
s=p.read_text()
issues=[]
# Remove unescaped TeX comments before delimiter/environment analysis.
t='\n'.join(re.split(r'(?<!\\)%', line, maxsplit=1)[0] for line in s.splitlines())
stack=[]
for n,c in enumerate(t):
    if c not in '{}': continue
    j=n-1
    while j>=0 and t[j]=='\\': j-=1
    if (n-1-j)%2: continue
    if c=='{': stack.append(n)
    elif not stack: issues.append(f'unmatched closing brace at {n}')
    else: stack.pop()
if stack: issues.append(f'{len(stack)} unclosed braces')
envs=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',t):
    typ,env=m.groups()
    if typ=='begin': envs.append(env)
    elif not envs or envs.pop()!=env: issues.append(f'environment mismatch: {env}')
if envs: issues.append(f'unclosed environments: {envs}')
keys=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',s)
cites=[]
for g in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',s): cites += [x.strip() for x in g.split(',')]
missing=sorted(set(cites)-set(keys))
if missing: issues.append(f'missing citations {missing}')
labels=re.findall(r'\\label\{([^}]+)\}',s)
refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',s)
if len(labels)!=len(set(labels)): issues.append('duplicate labels')
if set(refs)-set(labels): issues.append('undefined cross-references')
if re.search(r'\\(?:input|include|includegraphics)\b',s): issues.append('external TeX input dependency')
if s.count('\\begin{document}')!=1 or s.count('\\end{document}')!=1: issues.append('document boundaries invalid')
if s.count('\\newpage')<2: issues.append('orientation/contents page separation absent')
if '\\section*{Start here}' not in s: issues.append('orientation absent')
for phrase in ['historical draft','pseudofunctor','need not be faithful','not automatically ``deterministic','Syntax and observation','on representables','not a ladder of increasing generality']:
    if phrase not in s: issues.append(f'required distinction absent: {phrase}')
raw_words=len(s.split())
if not 4000<=raw_words<=6200: issues.append(f'guide length out of requested band: {raw_words}')
report={'artifact':'theory_guide.tex','sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'raw_whitespace_word_count':raw_words,'bibliography_entries':len(keys),'citation_occurrences':len(cites),'labels':len(labels),'issues':issues,'static_validation_passed':not issues,'compiled':False,'visual_layout_verified':False,'scope':'Brace/environment/citation/reference/dependency/required-content checks. These checks do not establish theorem correctness or rendered layout.'}
(ROOT/'artifact_validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
raise SystemExit(bool(issues))
