"""Local CPython timing probe; not part of deterministic archived replay."""
from hashlib import sha1
from pathlib import Path
from time import perf_counter
from statistics import median
import argparse,json,platform,sys
args=argparse.ArgumentParser()
args.add_argument('upstream')
args.add_argument('--leases',type=int,default=4096)
args.add_argument('--rounds',type=int,default=20)
args.add_argument('--trials',type=int,default=5)
a=args.parse_args()
src=Path(a.upstream).resolve()
for line in Path(__file__).with_name('SOURCE.tsv').read_text().splitlines():
    p,d=line.split('\t')
    b=(src/p).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==d
sys.path.insert(0,str(src))
from reuse import Edits,full,witnesses
from direct_incremental import update_with_witnesses
from indexed import Indexed
from fixture import modeled

def run(which):
    start=perf_counter()
    g,P=modeled(a.leases)
    if which=='indexed':i=Indexed(g)
    else:c=full(g)[0]
    ready=perf_counter()
    count=0
    for j in range(a.rounds):
        for cs,labels in (
           ({'choose_backup':True},set()),
           ({'main_bound':bool(j%2)},set()),
           ({'other_bound':True},{'safety'}),
           ({'late':True},{'safety','deadline'}),
           ({'other_bound':False},{'deadline'}),
           ({'late':False},set()),
        ):
            d,visits=P.update(cs,{})
            if which=='indexed':
                i.update(Edits(out=d)); proof=i.cache
            else:
                g,c,m=update_with_witnesses(g,c,Edits(out=d));proof=c
            assert {k for k,v in witnesses(proof,('safety','deadline')).items()
                    if v is not None}==labels
            count+=1
    finish=perf_counter()
    return [(ready-start)*1e3,(finish-ready)*1e3,count]

v={'old_copying_worklist':[],'indexed':[]}
for k in range(a.trials):
    for name in (list(v) if k%2==0 else list(reversed(v))):
        v[name].append(run(name))
result={k:{'setup_ms_median':round(median(t[0] for t in rows),3),
           'warm_ms_median':round(median(t[1] for t in rows),3),
           'warm_ms_trials':[round(t[1],3) for t in rows],
           'verified_verdicts_per_trial':rows[0][2]} for k,rows in v.items()}
print(json.dumps(dict(runtime=platform.python_version(),leases=a.leases,results=result,
                excludes='full shadow oracle per edit; includes incremental supplier + receiver + verdict'),
                sort_keys=True,indent=2))
