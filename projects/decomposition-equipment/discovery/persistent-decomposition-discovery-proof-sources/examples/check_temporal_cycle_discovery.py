#!/usr/bin/env python3
"""Exact event/state checks for temporal factor discovery. No third-party packages."""
import itertools,json
from pathlib import Path

def perms(d): return tuple(itertools.permutations(range(d)))
def comp(p,q): return tuple(p[q[x]] for x in range(len(p)))
def inv(p): return tuple(p.index(x) for x in range(len(p)))
def powp(p,k):
    z=tuple(range(len(p)))
    for _ in range(k): z=comp(p,z)
    return z

def hol(a):
    z=tuple(range(len(a[0])))
    for ai in a: z=comp(ai,z)
    return z

def roots(a):
    m=len(a); d=len(a[0]); H=hol(a); P=perms(d)
    return [(s,p) for s in P for p in P if comp(p,H)==comp(powp(s,m),p)]
def brute_factors(a,edges=None):
    m=len(a); d=len(a[0]); P=perms(d)
    if edges is None: edges=range(m)
    return [(s,ps) for s in P for ps in itertools.product(P,repeat=m)
            if all(comp(ps[(i+1)%m],a[i])==comp(s,ps[i]) for i in edges)]
def gauge_from_root(a,s,p0):
    ps=[p0]
    for ai in a[:-1]: ps.append(comp(comp(s,ps[-1]),inv(ai)))
    assert comp(comp(s,ps[-1]),inv(a[-1]))==p0
    return tuple(ps)
def macro_factor(a):
    m=len(a); d=len(a[0]); prefix=tuple(range(d)); ps=[]
    for ai in a: ps.append(inv(prefix)); prefix=comp(ai,prefix)
    H=hol(a)
    for i in range(m):
        for x in range(d):
            j=i;y=x
            for _ in range(m): y=a[j][y];j=(j+1)%m
            assert j==i and ps[i][y]==H[ps[i][x]]
    return tuple(ps),H

def main():
    out={'binary_cycles':[],'ternary_cycles':[]}
    binary_tables=0; proper_views=0
    for m in range(2,9):
        bad=good=0
        for pattern in itertools.product((0,1),repeat=m):
            a=tuple((0,1) if v==0 else (1,0) for v in pattern)
            rs=roots(a)
            # Closed form: even cycle only even holonomy; odd cycle both.
            assert bool(rs)==(m%2==1 or sum(pattern)%2==0)
            if m<=5:
                bf=brute_factors(a)
                assert len(bf)==len(rs)
                assert set(bf)=={(s,gauge_from_root(a,s,p)) for s,p in rs}
            macro_factor(a)
            bad+=not bool(rs); good+=bool(rs); binary_tables+=1
        # Every proper subset of actual edges of the odd twist has an exact identity factor.
        a=((0,1),)*(m-1)+((1,0),)
        P=perms(2)
        for mask in range((1<<m)-1):
            E=[i for i in range(m) if mask>>i&1]
            assert any(all(comp(ps[(i+1)%m],a[i])==ps[i] for i in E)
                       for ps in itertools.product(P,repeat=m))
            proper_views+=1
        out['binary_cycles'].append({'m':m,'edge_tables':2**m,'factorable':good,
            'nonfactorable':bad,'proper_views_of_odd_twist':2**m-1,
            'macro_time_factor_exists':True})
    for m in (2,3):
        count=success=0
        for a in itertools.product(perms(3),repeat=m):
            rs=roots(a); bf=brute_factors(a)
            assert set(bf)=={(s,gauge_from_root(a,s,p)) for s,p in rs}
            macro_factor(a)
            count+=1; success+=bool(rs)
        out['ternary_cycles'].append({'m':m,'edge_tables':count,'factorable':success})
    # Directly rule out any binary relation (including empty/nondeterministic) as a
    # component of the minimal four-state whole. Product equality retains events.
    target={(0,0,1,0),(0,1,1,1),(1,0,0,1),(1,1,0,0)}
    candidate_relations=0; exact_relations=0
    for mask in range(16):
        R={(x,y) for x in (0,1) for y in (0,1) if mask>>(2*x+y)&1}
        for ps in itertools.product(perms(2),repeat=2):
            image={(i,ps[i][b],j,ps[j][c]) for i,b,j,c in target}
            product={(i,x,1-i,y) for i in (0,1) for x,y in R}
            exact_relations+=image==product; candidate_relations+=1
    assert exact_relations==0
    # Controlled repair. Hidden fixed h is shown only at station0. Only lastedge
    # accepts c; b'=b XOR h XOR c there. Two-state memory stores h.
    control=[]
    for m in range(2,9):
        memoryless_ok=[]
        for c in (0,1):
            if all((h^c)==0 for h in (0,1)): memoryless_ok.append(c)
        assert not memoryless_ok
        for h,b0 in itertools.product((0,1),repeat=2):
            mem=h;b=b0
            for i in range(m):
                c=mem if i==m-1 else 0
                b=b^(h^c if i==m-1 else 0)
            assert b==b0
        # Structural identity factor is on calibrated I times BOTH orientation states.
        I={(i,h,z) for i in range(m) for h in (0,1) for z in (0,1) if i==0 or z==h}
        for i,h,z in I:
            z1=h if i==0 else z
            i1=(i+1)%m
            assert (i1,h,z1) in I
            for b in (0,1):
                b1=b^(h^z if i==m-1 else 0)
                assert b1==b
        control.append({'m':m,'memoryless_winning':0,'two_state_memory_wins':True,
            'calibrated_context_states':len(I),'binary_identity_factor_on_calibrated_domain':True,
            'completion_steps':m})
    # Noninvertible coprime-sampling control.
    F={(0,0):(0,0),(0,1):(0,0),(1,0):(0,1),(1,1):(0,0)}
    assert all(F[F[x]]==(0,0) and F[F[F[x]]]==(0,0) for x in F)
    assert F[(0,0)][1]!=F[(1,0)][1]
    out['noninvertible_coprime_counterexample']=True
    out.update(binary_edge_tables_checked=binary_tables,
               proper_edge_views_checked=proper_views,
               minimal_nondeterministic_relation_candidates=candidate_relations,
               minimal_exact_relations=exact_relations,
               controlled_repairs=control,all_assertions_passed=True)
    path=Path(__file__).with_name('temporal_cycle_discovery_results.json')
    path.write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
if __name__=='__main__': main()
