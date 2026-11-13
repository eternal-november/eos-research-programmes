"""Combine immutable v1 methods with one authorized corrected baseline run."""
import json
from pathlib import Path
P=Path(__file__).resolve().parent
original=json.loads((P/'mission_results.json').read_text())
corrected=json.loads((P/'corrected_rehearsal_results.json').read_text())
assert len(original['results'])==72 and len(corrected['results'])==12
assert original['protocol_sha256']==corrected['protocol_sha256']
key=lambda r:tuple(r[k] for k in ('n','L','s','seed','regime'))
replacement={key(r):r for r in corrected['results']}
results=[]
for r in original['results']:
 is_corrected=r['method']=='cached_rehearsal'
 row=dict(replacement[key(r)] if is_corrected else r)
 row['source_sha256']=(corrected if is_corrected else original)['source_sha256']
 row['source_result_file']='corrected_rehearsal_results.json' if is_corrected else 'mission_results.json'
 results.append(row)
final={'protocol_sha256':original['protocol_sha256'],'source_sha256':None,
 'source_sha256_by_method':{r['method']:r['source_sha256'] for r in results},
 'correction_description':'One authorized implementation bug correction: exactly predicted unsafe candidates now generate monotone cuts without physical replay. Same fixed instances and limits; other five methods unchanged. Original results preserved.',
 'results':results,'elapsed_seconds_original':original['elapsed_seconds'],'elapsed_seconds_corrected':corrected['elapsed_seconds']}
(P/'final_results.json').write_text(json.dumps(final))
print('Composed72 streams432 batches with per-method source provenance')
