"""Reproduce both deterministic selections from their frozen public universes.
No original source access is required for selection replay. This checks the
sampling record, not mathematical truth or original source-file availability.
"""
from pathlib import Path
import json,random,hashlib
if not __debug__:raise RuntimeError('Optimized execution is not a verified mode')
r=Path(__file__).resolve().parent; records=[]
for name in ['random_supporting_lemma_sample.json','broad_supporting_lemma_sample.json']:
 p=r/name; j=json.loads(p.read_text()); expected=random.Random(j['seed']).sample(j['universe'],min(6,len(j['universe'])))
 if expected!=j['sample']:raise RuntimeError('Sample differs from deterministic seeded selection: '+name)
 if j['universe_count']!=len(j['universe']):raise RuntimeError('Incorrect universe size: '+name)
 records.append({'file':name,'seed':j['seed'],'universe_count':len(j['universe']),'sample_count':len(expected),'selection_matches':True,'sample_record_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
out={'status':'PASS','records':records,'scope':'Selection replay from frozen ordered universes only. Does not certify proof truth, complete headline coverage, source retrieval, or source hash agreement.','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(r/'sample_replay_results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
