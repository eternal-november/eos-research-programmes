import re,json,sys,hashlib,collections,zipfile
from pathlib import Path
r=Path(sys.argv[1]);z=zipfile.ZipFile(sys.argv[2]);rows=json.loads((r/'TheoremIndex.json').read_text());audit=(r/'evidence/axioms.log').read_text()
a=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",audit,re.S)
assert [n for n,_ in a]==[x['declaration'] for x in rows] and len(set(n for n,_ in a))==len(rows)==2228
counts=collections.Counter(x.strip() for _,s in a if s for x in s.split(','))
assert set(counts)=={'propext','Classical.choice','Quot.sound'}
assert (r/'evidence/axioms.log').read_bytes()==z.read('evidence/axioms.log')
assert json.loads((r/'evidence/source_hashes.json').read_text())==json.loads(z.read('evidence/source_hashes.json'))
print('unique ordered axiom records',len(a),dict(counts),'axiom-free',sum(not v for _,v in a),'exact log match','85 rebuilt source hashes match')
