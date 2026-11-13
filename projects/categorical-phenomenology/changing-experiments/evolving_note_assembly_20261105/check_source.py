from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parent
p=root/'Changing_experiments_and_composing_characterizations.tex'
s=p.read_text()
# Strip TeX comments while respecting escaped percent signs.
t='\n'.join(re.split(r'(?<!\\)%',line)[0] for line in s.splitlines())
errors=[]; stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',t):
 typ,env=m.groups()
 if typ=='begin': stack.append((env,m.start()))
 elif not stack or stack[-1][0]!=env: errors.append(f'environment mismatch {env} at {m.start()}')
 else: stack.pop()
if stack: errors.append(f'unclosed environments {stack}')
brace=0
for i,c in enumerate(t):
 if c in '{}':
  bs=0;j=i-1
  while j>=0 and t[j]=='\\': bs+=1;j-=1
  if bs%2: continue
  brace += 1 if c=='{' else -1
  if brace<0: errors.append(f'extra closing brace at {i}'); brace=0
if brace: errors.append(f'brace balance {brace}')
labels=re.findall(r'\\label\{([^}]+)\}',t)
refs=re.findall(r'\\(?:eqref|ref|pageref)\{([^}]+)\}',t)
bibkeys=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^}]+)\}',t)
cites=[]
for keys in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',t): cites.extend(keys.split(','))
for kind,items in [('label',labels),('bibliography',bibkeys)]:
 if len(items)!=len(set(items)): errors.append(f'duplicate {kind}: {[x for x in set(items) if items.count(x)>1]}')
if set(refs)-set(labels): errors.append(f'missing references {set(refs)-set(labels)}')
if set(cites)-set(bibkeys): errors.append(f'missing citations {set(cites)-set(bibkeys)}')
for x in ['TODO','FIXME','PLACEHOLDER','\\input{','\\include{','\\bibliography{','\\includegraphics']:
 if x in t: errors.append(f'unexpected source marker {x}')
for start,end in [('\\[','\\]'),('\\(','\\)')]:
 if t.count(start)!=t.count(end): errors.append(f'math delimiter imbalance {start} {end}')
# Unescaped inline dollar count is a necessary, not sufficient, source check.
dollars=re.findall(r'(?<!\\)\$',t)
if len(dollars)%2: errors.append('odd inline dollar count')
report={'file':p.name,'bytes':len(s.encode()),'lines':len(s.splitlines()),'sha256':hashlib.sha256(s.encode()).hexdigest(),'environments_balanced':not stack,'labels':len(labels),'references':len(refs),'bibliography_entries':len(bibkeys),'citations':len(cites),'section_count':len(re.findall(r'\\section\{',t)),'errors':errors,'compiled':False,'proof_assistant_scope':'separate row quotient fragment only','status':'PASS' if not errors else 'FAIL'}
(root/'checks/source_integrity.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
sys.exit(bool(errors))
