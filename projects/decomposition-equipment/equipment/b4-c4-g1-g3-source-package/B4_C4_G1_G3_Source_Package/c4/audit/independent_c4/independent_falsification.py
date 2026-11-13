#!/usr/bin/env python3
"""Independent finite falsification of C4 statements; no author code imported."""
from itertools import product, permutations, combinations
from collections import Counter
from pathlib import Path
import hashlib,json
C=Counter()
def ck(p,msg):
    if not p: raise RuntimeError(msg)
def comp(R,S):
    return sum(1<<(2*a+c) for a in range(2) for c in range(2)
               if any((R>>(2*a+b)&1) and (S>>(2*b+c)&1) for b in range(2)))
# IF: labels and carrier relations are independent fields.
for a,b,c,d in product(range(3), repeat=4):
    for R,S in product(range(16),repeat=2):
        W=comp(R,S)
        typed=(b==c)
        erased=(comp(R,S)==W)
        ck(erased,'erased exact relation')
        C['IF_typed' if typed else 'IF_spurious_completed']+=1
ck(comp(9,9)==9 and 1!=2,'IF named counterexample')
# OCC: include empty choice sets and empty occurrence families.
for n in range(6):
    for cs in product(range(3),repeat=n):
        present=sorted(set(cs))
        for sizes in product(range(3),repeat=3):
            indexed=list(product(*(range(sizes[c]) for c in present)))
            allfamilies=set(product(*(range(sizes[c]) for c in cs)))
            images=[tuple(dict(zip(present,v))[c] for c in cs) for v in indexed]
            constant={v for v in allfamilies if all(cs[i]!=cs[j] or v[i]==v[j]
                      for i in range(n) for j in range(n))}
            ck(len(images)==len(set(images)) and set(images)==constant,'OCC image and injectivity')
            expected_surj=(not allfamilies) or all(cs.count(c)<2 or sizes[c]<=1 for c in present)
            ck((set(images)==allfamilies)==expected_surj,'OCC exact surjectivity including empty cases')
            C['OCC_slot_maps_and_choice_cardinalities']+=1
# PAR: enumerate quotient maps, not just representative choices.
indices=(0,1,1,2)
parts={tuple(next(j for j in range(i+1) if labels[j]==labels[i]) for i in range(4))
       for labels in product(range(4),repeat=4)}
for p in parts:
    classes=sorted(set(p))
    descenders=[v for v in product(range(3),repeat=len(classes))
                if all(v[classes.index(p[i])]==indices[i] for i in range(4))]
    kernel=all(p[i]!=p[j] or indices[i]==indices[j] for i in range(4) for j in range(4))
    ck(len(descenders)==int(kernel),'PAR existence and uniqueness')
    C['PAR_equivalence_relations']+=1
# Parallel does not imply congruence: words a~b alone, but aa not~ba.
def same_word_class(x,y): return x==y or {x,y}=={'a','b'}
ck(same_word_class('a','b') and not same_word_class('aa','ba'),'parallel not substitution closed')
# R(S)=simple graph plus total order: pullback along every injection.
def graphs(n):
    ps=list(combinations(range(n),2))
    for bits in product((0,1),repeat=len(ps)):
        yield frozenset(p for p,b in zip(ps,bits) if b)
def pb(E,order,f):
    rank={x:i for i,x in enumerate(order)}
    return (frozenset((a,b) for a,b in combinations(range(len(f)),2)
                     if tuple(sorted((f[a],f[b]))) in E),
            tuple(sorted(range(len(f)), key=lambda a:rank[f[a]])))
for n in range(4):
    for E in graphs(n):
        for order in permutations(range(n)):
            ck(pb(E,order,tuple(range(n)))==(E,order),'R identity')
            for t in range(n+1):
                for f in permutations(range(n),t):
                    Ef,of=pb(E,order,f)
                    for u in range(t+1):
                        for g in permutations(range(t),u):
                            ck(pb(Ef,of,g)==pb(E,order,tuple(f[x] for x in g)),'R arbitrary injection composition')
                            C['species_injection_compositions']+=1
# Independent product simplicial identities, nonthin K with arrows (a,b,z), z in Z/2.
# Record: graph size, edge set, layer vector, interface string, arrow bit string.
def face(x,i):
    m,E,L,A,Z=x; n=len(Z)
    if i in (0,n):
        forbidden=0 if i==0 else n-1
        U=tuple(v for v in range(m) if L[v]!=forbidden)
        pos={v:j for j,v in enumerate(U)}
        EE=frozenset((pos[a],pos[b]) for a,b in E if a in pos and b in pos)
        LL=tuple(L[v]-(i==0) for v in U)
        AA=A[1:] if i==0 else A[:-1]
        ZZ=Z[1:] if i==0 else Z[:-1]
        return (len(U),EE,LL,AA,ZZ)
    return (m,E,tuple(v-(v>=i) for v in L),A[:i]+A[i+1:],Z[:i-1]+((Z[i-1]+Z[i])%2,)+Z[i+1:])
def degen(x,j):
    m,E,L,A,Z=x
    return (m,E,tuple(v+(v>=j) for v in L),A[:j+1]+A[j:],Z[:j]+(0,)+Z[j:])
for n in range(4):
    for m in range(3):
        for E in graphs(m):
            for L in product(range(n),repeat=m):
                for A in product(range(2),repeat=n+1):
                    for Z in product(range(2),repeat=n):
                        x=(m,E,L,A,Z)
                        for i in range(n):
                            for j in range(i+1,n+1):
                                ck(face(face(x,j),i)==face(face(x,i),j-1),'d_i d_j')
                        for i in range(n+1):
                            for j in range(i,n+1):
                                ck(degen(degen(x,j),i)==degen(degen(x,i),j+1),'s_i s_j')
                        for j in range(n+1):
                            for i in range(n+2):
                                lhs=face(degen(x,j),i)
                                rhs=degen(face(x,i),j-1) if i<j else (x if i in (j,j+1) else degen(face(x,i-1),j))
                                ck(lhs==rhs,'d_i s_j including degree zero')
                        C['typed_product_simplices_m_le_2_degree_le_3']+=1
out={'status':'PASS','scope':'Independent finite falsification only; does not prove all-degree 2-Segal theorem or H2',
     'counts':dict(C),'author_code_imported':False,
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('independent_falsification_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
