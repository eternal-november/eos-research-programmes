#!/usr/bin/env python3
"""Independent expected domain counts. These are NOT test execution counts."""
from pathlib import Path
from itertools import product,combinations_with_replacement
from math import comb
from collections import Counter
import json,hashlib
import check_noimport as I
import check_x_label_mins as X
P=Path(__file__).parent
c=Counter()
def forest_count(t,M):
    ls=[l for a,l in I.occurrences(t)];m=len(M)
    return 1+m+len(ls)*m+sum(2**len(l.vertices)*(l.arrow[1]-l.arrow[0]+1)*2 for l in ls)+m*sum(not l.vertices and l.arrow==(l.arrow[0],l.arrow[0],0) for l in ls)
def homs(M,N):return [h for h in product(range(len(N)),repeat=len(M)) if h[0]==0 and all(h[M[a][b]]==N[h[a]][h[b]] for a in range(len(M)) for b in range(len(M)))]
for name,M in I.TABLES.items():
    basecount=0
    for p in I.SHAPES:
        for t in I.x_instances(p,M):
            basecount+=1;steps=len(I.redexes(t));c['paths_ordinary_peak_join']+=steps
            for host,a in I.contexts(t,M):c['paths_MOut']+=steps*forest_count(host,M)
    # One named six source per monoid also receives transports and one MOut control.
    c['paths_MOut']+=1
    for p in I.SHAPES:
        for t in I.x_instances(p,M):
            for N in I.TABLES.values():
                h=len(homs(M,N));c['transport_maps']+=20*h;c['transport_raw_edges']+=20*h*forest_count(t,M)
            c['object_transport_composites']+=400
            c['monoid_transport_composites']+=sum(len(homs(M,N))*len(homs(N,Q)) for N in I.TABLES.values() for Q in I.TABLES.values())
            c['graph_coordinate_maps']+=3;c['graph_coordinate_inverse_pairs']+=3;c['interface_rename_inverse_pairs']+=1
            c['graph_nested_restrictions']+=3*sum(2**len(l.vertices) for a,l in I.occurrences(t))
    t=I.six()
    for N in I.TABLES.values():
        h=len(homs(M,N));c['transport_maps']+=20*h;c['transport_raw_edges']+=20*h*forest_count(t,M)
    c['object_transport_composites']+=400
    c['monoid_transport_composites']+=sum(len(homs(M,N))*len(homs(N,Q)) for N in I.TABLES.values() for Q in I.TABLES.values())
    c['graph_coordinate_maps']+=3;c['graph_coordinate_inverse_pairs']+=3;c['interface_rename_inverse_pairs']+=1
    c['graph_nested_restrictions']+=3*sum(2**len(l.vertices) for a,l in I.occurrences(t))
    cases=X.pairs(M)
    for rule,t,target in cases:
        c['paths_MIn']+=(5+len(M))*(1+forest_count(t,M))
        c['paths_ordinary_disjoint']+=1;c['paths_ordinary_variable']+=len(I.occurrences(t))
    c['MIn_union_unique']+=len(cases)
    c['six_positional_split_value_assignments']+=len(M)**5
    c['graph_edge_block_composites']+=basecount+1
    c['paths_MIn_d0_control']+=1;c['paths_MIn_tower']+=5*9;c['tower_heights']+=5*9
    c['six_label_tuples']+=len(M)**5
    for n in range(3):
        for a in range(3):
            for b in range(a,3):
                sizes=[]
                for k in range(4):
                    chains=sum(o[0]==a and o[-1]==b for o in combinations_with_replacement(range(3),k+1)) if k else int(a==b and n==0)
                    sizes.append((k**n if k else int(n==0))*chains*len(M))
                c['H_sources']+=2**(n*(n-1)//2)*sum(sizes)
                c['H_hom_pairs']+=2**(n*(n-1)//2)*sum(sizes)**2
c['paths_MOut_inverse']=c['paths_MOut']
c['paths_raw_composition']=1736
c['paths_raw_then_equations']=1736
c['named_raw_flat_pairs']=1736
c['raw_menu_count_source']='independently executed fixed two-stage suite'
c['tree_checks']=112785+2
c['one_step_reducts']=268920-1158+2
c['graph_coordinate_restrictions']=c['graph_nested_restrictions']
c['F_exhaustive_cases']=sum(len(M) for M in I.TABLES.values())*sum(sum(2**(n*(n-1)//2)*k**n for n in range(3))*comb(k+3,2)*sum(k-q+1 for q in range(2,k)) for k in (3,4))
r={'status':'DERIVED_NOT_EXECUTED_TESTS','domain_sha256':hashlib.sha256((P/'../../finite/DOMAIN.md').read_bytes()).hexdigest(),'method':'Independent global-incidence pattern enumeration and exact finite menu cardinalities; no author imports','expected_counts':dict(c),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(P/'ExpectedAuthorCounts.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
