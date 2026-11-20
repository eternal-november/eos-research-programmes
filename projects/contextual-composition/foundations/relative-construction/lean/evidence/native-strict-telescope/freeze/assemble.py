"""Rebuild a full source tree from the exact merge-235 project + source only differential."""
from pathlib import Path
import hashlib,json,re,shutil,sys,os
p=Path(__file__).resolve().parent; base=Path(sys.argv[1]); dest=Path(sys.argv[2]); assert not dest.exists();dest.mkdir(parents=True)
H=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
parent=json.loads((p/'parent.json').read_text()); assert len(parent)==490
assert H(p/'parent.json')=='e94f897ea9fcc98534d40fbd0bce1cdc8c38f3fea73a57291af0e57e77d526c8'
actual=set()
for root,dirs,files in os.walk(base):
 here=Path(root).relative_to(base)
 if here==Path('.'):dirs[:]=[n for n in dirs if n not in ('.git','.lake','evidence')]
 actual.update(str(here/f) for f in files)
assert actual==set(parent),(sorted(actual-set(parent)),sorted(set(parent)-actual))
for k,v in parent.items():
 assert H(base/k)==v,k
 d=dest/k;d.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(base/k,d)
mods=(p/'modules.txt').read_text().splitlines()
rows=[]
for f in sorted((p/'overlay').rglob('*')):
 if not f.is_file():continue
 k=f.relative_to(p/'overlay');assert str(k) not in parent
 shutil.copyfile(f,dest/k)
for n in mods:
 k='ContextualComposition/'+n+'.lean';ns=None
 for l in (dest/k).read_text().splitlines():
  if l.startswith('namespace ContextualComposition.'):ns=l.split()[1]
  m=re.match(r"^(?:noncomputable )?(?:theorem|def|abbrev|structure|inductive|instance) ([\w\u0080-\uffff']+)",l)
  if m:assert ns;rows.append({'declaration':ns+'.'+m[1],'file':k})
orig=json.loads((base/'TheoremIndex.json').read_text());assert len(orig)==4724 and len(set(r['declaration'] for r in orig+rows))==len(orig+rows)
(dest/'TheoremIndex.json').write_text(json.dumps(orig+rows,indent=2)+'\n')
(dest/'AxiomAudit.lean').write_text((base/'AxiomAudit.lean').read_text()+''.join('#print axioms '+r['declaration']+'\n' for r in rows))
(dest/'ContextualComposition.lean').write_text((base/'ContextualComposition.lean').read_text()+''.join('public import ContextualComposition.'+n+'\n' for n in mods))
hs={str(f.relative_to(dest)):H(f) for f in sorted(dest.rglob('*')) if f.is_file()}
assert len(hs)==490+len(mods)+len(list((p/'overlay/checks').glob('*.lean')))
if (p/'final-source.json').exists():assert hs==json.loads((p/'final-source.json').read_text())
else:(p/'final-source.json').write_text(json.dumps(hs,sort_keys=True,indent=2)+'\n')
print('parent 490,',len(hs),'final sources;',len(mods),'new production modules;',len(rows),'new names;',len(orig+rows),'total;',len(list((dest/'checks').glob('*.lean'))),'official probes')
