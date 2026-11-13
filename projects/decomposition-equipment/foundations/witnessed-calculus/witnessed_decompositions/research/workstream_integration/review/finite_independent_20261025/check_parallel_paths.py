#!/usr/bin/env python3
"""Fixed named parallel paths: all finite source/local values, no author imports."""
from pathlib import Path
from itertools import product
from collections import defaultdict,Counter
import json,hashlib
import check_noimport as I
P=Path(__file__).parent;c=Counter()
def reduction_path(t,M):
    out=[];q=t
    for address,rule in I.normal(t,M)[1]:
        q=I.rewrite(q,address,rule,M);out.append(I.eq(q,address,rule,M))
    return tuple(out)
for name,M in I.TABLES.items():
    empty=I.leaf((),(),(1,1,0));two=I.cut(empty,empty,())
    F=(empty,two);H=(two,empty)
    left=I.path(two,(I.raw(F),),M)
    target=I.graft(two,F)
    right=I.path(two,(I.raw(H),I.eq(target,(),'R',M)),M)
    assert left[0]==right[0] and left[1]!=right[1] and left[2]!=right[2]
    assert I.compose(I.flat(two,M),left[2],M)==I.compose(I.flat(two,M),right[2],M)
    c['segmentation_parallel_path_pairs']+=1
    for mode,base in (('six_unary',I.six()),('two_nullary',two)):
        for value in range(len(M)):
            source=I.val(value,base);groups=defaultdict(list)
            leaves=[l for a,l in I.occurrences(base)]
            for values in product(range(len(M)),repeat=len(leaves)):
                F=tuple(I.val(v,l if mode=='six_unary' else I.unit(l.arrow[0])) for v,l in zip(values,leaves))
                target=I.graft(source,F)
                result=I.path(source,(I.raw(F),)+reduction_path(target,M),M)
                groups[result[0]].append(result)
                assert tuple(w[5] for w in result[2])==values
                assert all(len(w[3])==(1 if mode=='six_unary' else 0) for w in result[2])
                c[mode+'_paths']+=1
            for endpoint,rows in groups.items():
                assert len({r[1] for r in rows})==len(rows)==len({r[2] for r in rows})
                c['derived_'+mode+'_distinct_parallel_pairs']+=len(rows)*(len(rows)-1)//2
r={'status':'PASS','fixed_domain':'Z3/E2/One; six source all m^5 scalar assignments and two-empty nullary all m^3 assignments; canonical equation paths to shared endpoints; one segmentation pair per monoid','counts':dict(c),'accounting':'All paths and set-uniqueness assertions executed. Keys prefixed derived_ count unordered distinct parallel pairs by n(n-1)/2 after injectivity check; individual pairwise comparisons were not executed.','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'engine_sha256':hashlib.sha256((P/'check_noimport.py').read_bytes()).hexdigest()}
(P/'ParallelPathCertificate.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
