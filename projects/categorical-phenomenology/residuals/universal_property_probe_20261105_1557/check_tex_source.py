#!/usr/bin/env python3
"""Static integrity check only. Does not compile or validate mathematical proofs."""
from pathlib import Path
import re,json,hashlib
p=Path(__file__).with_name('Controlled_training_responses.tex')
raw=p.read_text();s=re.sub(r'(?<!\\)%[^\n]*','',raw)
errors=[];stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',s):
 if m[1]=='begin':stack.append(m[2])
 elif not stack or stack.pop()!=m[2]:errors.append('environment mismatch at '+m.group())
if stack:errors.append('unclosed environments '+str(stack))
level=0;i=0
while i<len(s):
 if s[i]=='\\' and i+1<len(s) and s[i+1] in '\\{}%':i+=2;continue
 if s[i]=='{':level+=1
 elif s[i]=='}':
  level-=1
  if level<0:errors.append('premature closing brace');break
 i+=1
if level:errors.append('unbalanced braces '+str(level))
labels=re.findall(r'\\label\{([^}]+)\}',s)
refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',s)
bib=re.findall(r'\\bibitem\{([^}]+)\}',s)
cites=[c.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',s) for c in group.split(',')]
if len(set(labels))!=len(labels):errors.append('duplicate label')
if len(set(bib))!=len(bib):errors.append('duplicate bibliography key')
errors += ['undefined reference '+r for r in refs if r not in labels]
errors += ['undefined citation '+c for c in cites if c not in bib]
if re.search(r'\\(?:input|include|bibliography)\s*\{',s):errors.append('external TeX input')
report={'source':p.name,'bytes':len(raw.encode()),'sha256':hashlib.sha256(raw.encode()).hexdigest(),'label_count':len(labels),'reference_count':len(refs),'bibliography_entries':len(bib),'citation_uses':len(cites),'errors':errors,'compiled':False,'scope':'Static brace, environment, cross-reference and bibliography integrity; no rendering or proof-assistant claim.'}
p.with_name('source_integrity.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
assert not errors
