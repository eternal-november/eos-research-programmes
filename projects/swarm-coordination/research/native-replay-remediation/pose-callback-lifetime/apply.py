"""Apply a checked overlay to an explicitly supplied exact archive root."""
from pathlib import Path
from hashlib import sha256
import sys
bundle=Path(__file__).parent
pr,root=sys.argv[1:];root=Path(root)
def digest(v):return sha256(v).hexdigest()
[k,p,ref,old,new,e]=next(s.split("\t") for s in (bundle/"REPLAY_PATCH.tsv").read_text().splitlines() if s.startswith(pr+"\t"))
replacement=(bundle/k/'mission.cpp').read_bytes()
assert digest(replacement)==new
assert digest((root/'mission.cpp').read_bytes())==old
assert digest((root/'EXPECTED.jsonl').read_bytes())==e
(root/'mission.cpp').write_bytes(replacement)
(root/'MANIFEST.sha256').write_bytes((bundle/k/'MANIFEST.sha256').read_bytes())
