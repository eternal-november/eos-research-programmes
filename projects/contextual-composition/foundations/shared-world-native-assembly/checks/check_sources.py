"""Local TeX environment/reference and package-link checks; no TeX compilation."""
from pathlib import Path
import re,json
root=Path(__file__).resolve().parent.parent
results=[]
for p in sorted(root.glob('*.tex')):
 s=p.read_text();stack=[]
 for op,name in re.findall(r'\\(begin|end)\{([^}]+)\}',s):
  if op=='begin':stack.append(name)
  else:assert stack and stack.pop()==name,(p,name)
 assert not stack,p
 labels=re.findall(r'\\label\{([^}]+)\}',s)
 assert len(labels)==len(set(labels)),p
 refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',s)
 assert not(set(refs)-set(labels)),(p,set(refs)-set(labels))
 results.append({'file':p.name,'labels':len(labels),'references':len(refs)})
for link in re.findall(r'\]\(([^)]+)\)',(root/'README.md').read_text()):
 if not link.startswith(('http','../')):assert(root/link).exists(),link
print(json.dumps({'status':'PASS','sources':results,'scope':'environment/reference/local-package links only; no TeX compilation'},indent=2))
