"""Exact finite checks for witnessed feedback composition.
No probability grid is used: small positive marginal systems are solved by
rational basic-feasible-support enumeration. Finite examples support, not prove,
the written unbounded statements.
"""
from fractions import Fraction as Q
from itertools import product, combinations, permutations
import json


def solve_columns(A, b, cols):
    """Solve A[:,cols] x=b when its columns are independent."""
    n=len(cols)
    rows=[[Q(row[j]) for j in cols]+[Q(rhs)] for row,rhs in zip(A,b)]
    pivot=0
    for j in range(n):
        k=next((k for k in range(pivot,len(rows)) if rows[k][j]),None)
        if k is None:
            return None
        rows[pivot],rows[k]=rows[k],rows[pivot]
        z=rows[pivot][j]
        rows[pivot]=[x/z for x in rows[pivot]]
        for k in range(len(rows)):
            if k!=pivot and rows[k][j]:
                z=rows[k][j]
                rows[k]=[x-z*y for x,y in zip(rows[k],rows[pivot])]
        pivot+=1
    if any(not any(row[:n]) and row[n] for row in rows):
        return None
    x=[rows[j][n] for j in range(n)]
    if min(x,default=Q(0))<0:
        return None
    return x


def positive_law(points, moments):
    """Exact feasibility in simplex with rational equality moments.

    A nonempty compact probability polytope has a vertex. Its positive support
    columns are independent, so the finite enumeration is complete here.
    """
    A=[[Q(1)]*len(points)]
    b=[Q(1)]
    for f,rhs in moments:
        A.append([Q(f(x)) for x in points]);b.append(Q(rhs))
    for n in range(1,min(len(A),len(points))+1):
        for cols in combinations(range(len(points)),n):
            x=solve_columns(A,b,cols)
            if x is not None:
                p={z:Q(0) for z in points}
                for j,w in zip(cols,x):p[points[j]]=w
                assert all(sum(w*f(z) for z,w in p.items())==rhs for f,rhs in moments)
                assert sum(p.values())==1
                return p
    return None


def pair_rows(i,j,parity):
    return [(lambda x,i=i,j=j,a=a,b=b:int(x[i]==a and x[j]==b),
             Q(int((a^b)==parity),2)) for a,b in product((0,1),repeat=2)]

bits=(0,1)
triples=list(product(bits,repeat=3))
first=pair_rows(0,1,1)+pair_rows(1,2,1)
second=pair_rows(0,1,1)+pair_rows(0,2,1)
assert positive_law(triples,first) is not None
assert positive_law(triples,second) is not None
assert positive_law(triples,first+second) is None
repair=positive_law(triples,first+pair_rows(0,2,0))
assert {x:w for x,w in repair.items() if w}=={(0,1,0):Q(1,2),(1,0,1):Q(1,2)}


def greatest_invariant(states,actions,events,step):
    C=set(states)
    while True:
        D={s for s in C if all(step(s,a,e) in C for a in actions for e in events)}
        if D==C:return C
        C=D

# Fixed-encoding fair-bit example: no nonempty innovation support works.
diagonal={(0,0),(1,1)}
E=list(product(bits,repeat=2))
fixed_step=lambda s,a,e:(e[0],e[1]^a)
fixed_success=0
for n in range(1,len(E)+1):
    for L in combinations(E,n):
        C=greatest_invariant(diagonal,bits,L,fixed_step)
        if C:
            law=positive_law(list(L),[(lambda e:int(e[0]==0),Q(1,2)),
                                     (lambda e:int(e[1]==0),Q(1,2))])
            fixed_success+=int(law is not None)
assert fixed_success==0
# Same source u and licensed second-side recoding e2=u XOR a succeeds.
recoded_step=lambda s,a,u:(u,(u^a)^a)
assert greatest_invariant(diagonal,bits,bits,recoded_step)==diagonal
# Check pathwise feedback for all four deterministic observation policies.
for policy in product(bits,repeat=2):
    for init in diagonal:
        for source in product(bits,repeat=4):
            s=init
            for u in source:
                a=policy[s[0]]
                s=recoded_step(s,a,u)
                assert s[0]==s[1]

# Recoder-law rows depending on reachable support invalidate the largest-state
# shortcut: state 1 is transition-invariant but violates a fair-output recoder.
identity_step=lambda s,a,u:s
assert greatest_invariant(bits,bits,bits,identity_step)==set(bits)
recoder=lambda s,u:u if s==0 else 0
fair_at=lambda s:all(sum(Q(1,2) for u in bits if recoder(s,u)==v)==Q(1,2) for v in bits)
assert fair_at(0) and not fair_at(1)
assert greatest_invariant({0},bits,bits,identity_step)=={0}
# Initial delta_0 and retained C={0} give a valid reachable-only witness.

# Persistent unknown parity versus illicit timewise reselection.
one_step={theta:{(a,b,a^b^theta) for a,b in product(bits,repeat=2)} for theta in bits}
persistent={(x,y) for theta in bits for x in one_step[theta] for y in one_step[theta]}
rectangular=set(product(triples,repeat=2))
assert len(persistent)==32 and len(rectangular)==64
assert all((x[0]^x[1]^x[2])==(y[0]^y[1]^y[2]) for x,y in persistent)
assert len(rectangular-persistent)==32

# Graph-only original C5 crossing criterion, all ordered nonempty partitions
# of <=4 vertices. Vertex permutations suffice: any common refinement can be
# further split into singleton identity-arrow occurrences.
cases=0
for n in range(1,5):
    partitions=[]
    for k in range(1,n+1):
        partitions.extend(p for p in product(range(k),repeat=n) if set(p)==set(range(k)))
    orders=list(permutations(range(n)))
    for u,v in product(partitions,repeat=2):
        inversion=any(u[x]<u[y] and v[x]>v[y] for x,y in product(range(n),repeat=2))
        actual=any(all(u[p[t]]<=u[p[t+1]] and v[p[t]]<=v[p[t+1]]
                       for t in range(n-1)) for p in orders)
        assert actual==(not inversion)
        cases+=1

# Conditional deterministic circuit composition. A shared event (a,b,c) is
# projected, not independently redrawn; two owner schedules give same output.
for old,action,event in product(product(bits,repeat=3),bits,triples):
    expected=tuple(old[i]^action^event[i] for i in range(3))
    for owners in [((0,1),(2,)),((0,2),(1,))]:
        tape={'old':old,'action':action,'event':event,'out':{}}
        for block in owners:
            for i in block:
                tape['out'][i]=tape['old'][i]^tape['action']^tape['event'][i]
        result=tuple(tape['out'][i] for i in range(3))
        assert result==expected

print(json.dumps({'status':'PASS','positive_triangle_incompatible':True,
 'positive_repair_support':[list(x) for x,w in repair.items() if w],
 'fixed_seed_successful_supports':fixed_success,'recoding_feedback_horizon':4,
 'reachable_recoder_domain_requires_state_support_search':True,
 'persistent_two_step_support':len(persistent),'resampled_two_step_support':len(rectangular),
 'ordered_crossing_partition_pairs_checked':cases,
 'conditional_update_owner_schedules_checked':2},indent=2))
