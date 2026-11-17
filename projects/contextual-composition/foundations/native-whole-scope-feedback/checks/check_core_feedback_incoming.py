import runpy,json
from fractions import Fraction as F
from pathlib import Path
ns=runpy.run_path(str(Path(__file__).with_name('check_core_feedback_instance.py')))
raw,Q=ns['raw'],ns['Q']
R=range(3); f=lambda r:0 if r<2 else 2
source={(a,r):(q if r==a[0][0] else F(0)) for a,q in Q.items() for r in R}
target={(a,r):F(0) for a in raw for r in R}
for (a,r),q in source.items():target[a,f(r)]+=q
assert len(source)==1323 and len(target)==1323
assert [sum(q for (a,s),q in source.items() if s==r) for r in R]==[F(1,2),F(1,2),F(0)]
assert [sum(q for (a,s),q in target.items() if s==r) for r in R]==[F(1),F(0),F(0)]
for a in raw:
 assert sum(source[a,r] for r in R)==sum(target[a,r] for r in R)==Q[a]
print(json.dumps({'signature_raw_atoms':len(source),'reserve_marginal_push':'PASS','whole_local_law_retained':'PASS','target_off_image_atom_retained':True,'scope':'finite raw/law check; coefficient identities and categorical squares proved in text'},indent=2))
