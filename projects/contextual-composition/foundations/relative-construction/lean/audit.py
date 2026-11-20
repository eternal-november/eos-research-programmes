"""Verify the complete, ordered, named declaration audit after lake build."""
from pathlib import Path
import json,re,hashlib,collections
p=Path(__file__).resolve().parent
rows=json.loads((p/'TheoremIndex.json').read_text()); n=[r['declaration'] for r in rows]
assert len(n)==len(set(n)) and re.findall(r'^#print axioms (\S+)$',(p/'AxiomAudit.lean').read_text(),re.M)==n
s=(p/'evidence/axioms.log').read_bytes(); lines=[re.sub(r'\s+',' ',a).strip() for a in re.split(r"(?m)(?=^'[^']+' )",s.decode()) if a.strip()];names=[];cnt=collections.Counter()
for line in lines:
    m=re.fullmatch(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",line);assert m,line
    names.append(m[1])
    if m[2]:cnt.update(m[2].split(', '))
assert names==n and set(cnt)<={'Classical.choice','propext','Quot.sound'}
for f in [*p.glob('ContextualComposition/*.lean'),*p.glob('checks/*.lean'),p/'ContextualComposition.lean']:
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',f.read_text()),f
print('PASS:',len(n),'ordered unique declaration audits; axiom counts',dict(cnt),'transcript sha256',hashlib.sha256(s).hexdigest())
