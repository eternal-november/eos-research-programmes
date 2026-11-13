#!/usr/bin/env python3
"""Independent exhaustive threshold-memory check, not a mission run."""
from pathlib import Path
import hashlib,itertools,json,random
import numpy as np
from relational_engine import Catalogue,ForestKnowledge,iter_ids

ROOT=Path(__file__).resolve().parent

def scalar(d,c):
    bits=[int(c[p]>=r) for p,r in d['features']]
    return (d['table']>>sum(v<<j for j,v in enumerate(bits)))&1


def main():
    cat=Catalogue(2,2)
    # Independent product enumeration used only by this test oracle.
    worlds=np.array(list(itertools.product(range(cat.size),repeat=3)),dtype=np.int16)
    contexts=list(itertools.product(range(3),repeat=2))
    predictions={c:np.array([scalar(cat.describe(h),c) for h in range(cat.size)],dtype=np.uint8) for c in contexts}
    checks=0
    for seed in range(202610292300,202610292308):
        rng=random.Random(seed); truth=[rng.randrange(cat.size) for _ in range(3)]
        k=ForestKnowledge(cat,3); surviving=worlds.copy()
        for step in range(8):
            c=rng.choice(contexts)
            a,b=((0,1) if step%2==0 else (1,2))
            total=int(predictions[c][truth[a]]+predictions[c][truth[b]])
            assert k.observe_sum(a,b,c,total)
            keep=predictions[c][surviving[:,a]]+predictions[c][surviving[:,b]]==total
            surviving=surviving[keep]
            for u in range(3):
                assert set(iter_ids(k.domains[u]))==set(map(int,surviving[:,u]));checks+=1
            for q in contexts:
                for i,j in itertools.combinations(range(3),2):
                    exact=set(map(int,predictions[q][surviving[:,i]]+predictions[q][surviving[:,j]]))
                    assert set(k.possible_sum(i,j,q))==exact;checks+=1
            # Mixed-time assignments explicitly require one persistent function.
            for rep in range(5):
                queries=[(rng.randrange(3),rng.choice(contexts),rng.randrange(2)) for _ in range(3)]
                mask=np.ones(len(surviving),dtype=bool)
                for u,q,bit in queries:mask &= predictions[q][surviving[:,u]]==bit
                assert k.feasible(queries)==bool(mask.any());checks+=1
    result={'passed':True,'n_ports':2,'L':2,'outputs':3,'catalogue_size':cat.size,
            'full_worlds_enumerated_by_test_only':len(worlds),'seeds':list(range(202610292300,202610292308)),
            'evidence_prefixes':64,'exact_comparisons':checks,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'engine_sha256':hashlib.sha256((ROOT/'relational_engine.py').read_bytes()).hexdigest()}
    (ROOT/'partial_acquisition_reference_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
