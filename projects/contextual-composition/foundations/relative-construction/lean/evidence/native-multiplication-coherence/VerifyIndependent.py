"""Independent source and transcript checks; run from a directory with inputs/, pkg/ and receipts."""
from pathlib import Path
from collections import Counter
from datetime import datetime,timezone
import json,hashlib,re
p=Path(__file__).resolve().parent
q=p/'pkg'; inp=p/'inputs'
sha=lambda data:hashlib.sha256(data).hexdigest()
blob=lambda data:hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
src=json.loads((inp/'final-source.json').read_text())
assert len(src)==153 and all(sha((q/k).read_bytes())==v for k,v in src.items())
aggregate=sha(b''.join(k.encode()+b'\0'+bytes.fromhex(src[k]) for k in sorted(src)))
assert aggregate=='9d4fc98c3fae86dbe33d002f9df81777cf5170bc863217c2e13af44b29f43034'
prov=json.loads((p/'Provenance.json').read_text())['remoteGitBlobs']
assert prov==json.loads((inp/'baseline.json').read_text()) and len(prov)==140
mods={'TheoremIndex.json','ContextualComposition.lean','AxiomAudit.lean'}
assert {k for k,v in prov.items() if blob((q/k).read_bytes())!=v}==mods
idx=json.loads((q/'TheoremIndex.json').read_text());new=json.loads((inp/'additions.json').read_text())
assert idx[2712:]==new
for k in ['TheoremIndex.json']:
 raw=(json.dumps(idx[:2712],indent=2)+'\n').encode();assert blob(raw)==prov[k]
audittext=(q/'AxiomAudit.lean').read_text()
resid=audittext.removesuffix(''.join('#print axioms '+row['declaration']+'\n' for row in new))
assert blob(resid.encode())==prov['AxiomAudit.lean']
amods=list(dict.fromkeys(Path(row['file']).stem for row in new))
assert len(amods)==9
allimp=(q/'ContextualComposition.lean').read_text();assert blob(allimp.removesuffix(''.join('public import ContextualComposition.'+m+'\n' for m in amods)).encode())==prov['ContextualComposition.lean']
actual=(q/'evidence/axioms.log').read_bytes()
line=re.compile(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)\s*",re.S)
r=[];a=Counter();pos=0; transcript=actual.decode()
while pos<len(transcript):
 m=line.match(transcript,pos)
 assert m is not None, repr(actual[pos:pos+100])
 pos=m.end();r.append(m[1])
 if m[2]:a.update(x.strip() for x in m[2].split(','))
assert len(r)==len(set(r))==2849 and r==[z['declaration'] for z in idx] and set(a)<={'Classical.choice','Quot.sound','propext'}
assert all(x['pin']==x['head'] and not x['trackedStatus'] and not x['untrackedLeanOrOlean'] for x in json.loads((p/'Dependencies.json').read_text()))
assert set(x.name for x in (q/'.lake/build/lib/lean/ContextualComposition').glob('*.olean'))==set(x.with_suffix('.olean').name for x in (q/'ContextualComposition').glob('*.lean'))
ts=lambda f:datetime.fromtimestamp(f.stat().st_mtime,timezone.utc).isoformat()
print('Verified 140 remote Git blobs at #225; 153 final source hashes; only three additive aggregates changed; nine new modules; source digest',aggregate)
print('Verified nine pinned HEADs with no tracked worktree changes or nonignored untracked Lean/olean files. Cached dependency binaries were not rebuilt.')
print('Independent full-transcript parse: 2849 unique ordered names (2712 + 137). Axiom frequencies:',dict(sorted(a.items())),'SHA256',sha(actual))
print('Project modules independently rebuilt:',len(list((q/'ContextualComposition').glob('*.lean'))),'+ aggregate. Aggregate build log:',sha((q/'evidence/build.log').read_bytes()))
print('Observed files at UTC: Lean version/pre-build',ts(q/'lean-version.log'),'build.log (lake build returned)',ts(q/'evidence/build.log'),'axioms.log (Lean transcript process returned)',ts(q/'evidence/axioms.log'))
