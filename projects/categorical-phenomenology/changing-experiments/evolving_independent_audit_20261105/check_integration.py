#!/usr/bin/env python3
from itertools import product
import json
from pathlib import Path
from check_independent import extents, rows, faces, canon, close

S=tuple(product((0,1),repeat=2))
source=set();target={frozenset({(1,1)})}
counts={'source':{'rows':len(rows(S,source)),'extents':len(extents(S,source)),'faces':len(faces(S,source))},
        'target':{'rows':len(rows(S,target)),'extents':len(extents(S,target)),'faces':len(faces(S,target))}}
assert counts=={'source':{'rows':1,'extents':1,'faces':0},'target':{'rows':2,'extents':2,'faces':1}}

# Native cyclic gap, evaluated by enumerating all concrete synchronized words.
cases=0
for K in range(1,6):
    for n in range(9):
        words=list(product((0,1),repeat=n))
        f=lambda w:sum(1 if b==0 else K+1 for b in w)
        g=lambda w:sum(K+1 if b==0 else 1 for b in w)
        L=min(map(f,words))+min(map(g,words))
        J=min(f(w)+g(w) for w in words)
        assert L==2*n and J==(K+2)*n
        cases+=1

H=('a','b','c');old={frozenset({'a'}),frozenset(H)};A=frozenset({'a','c'});U=frozenset({'a','b'})
left=close(H,old,A&U)&U;right=close(H,old,A)&U
assert left==frozenset({'a'}) and right==U

# Equal labelled test actions do not determine raw state maps.
state=(0,1);only_test=frozenset(state);f=(0,0);g=(1,1)
assert f!=g
assert frozenset(x for x in state if f[x] in only_test)==frozenset(x for x in state if g[x] in only_test)==only_test

out={'paired_batch_incidence_counts':counts,'native_cyclic_gap_cases':cases,
     'mixed_restriction_strictness':{'left':sorted(left),'right':sorted(right)},
     'nonseparating_tests_do_not_determine_raw_maps':True,'errors':[]}
Path(__file__).with_name('integration_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
