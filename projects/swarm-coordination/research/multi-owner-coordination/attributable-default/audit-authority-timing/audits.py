"""Exact single-public-mask audit feasibility and schedule construction."""
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
import json

def subsets(n):
    for m in range(1,n+1):
        yield from combinations(range(n),m)

def bound(edges,caps,r):
    """Threshold plus a nonempty cut/index attaining it."""
    C=[(1-x,('individual',i)) for i,x in enumerate(r)]
    for X in subsets(len(r)):
        U=set().union(*(edges[i] for i in X))
        C.append(((sum(caps[j] for j in U)-sum(r[i] for i in X))/len(X),('cut',X)))
    return min(C,key=lambda x:x[0])

def integer_flow(edges,caps,demands,Q):
    n=len(demands); m=len(caps); s=n+m;t=s+1
    g=[{} for _ in range(t+1)]
    def add(a,b,k):
        g[a][b]=k;g[b][a]=0
    for i,w in enumerate(demands):
        add(s,i,w)
        for j in edges[i]:add(i,n+j,Q)
    for j,k in enumerate(caps):add(n+j,t,k*Q)
    delivered=0
    while True:
        parent={s:None}; pending=[s]
        for a in pending:
            if a==t: break
            for b,w in g[a].items():
                if w>0 and b not in parent:
                    parent[b]=a;pending.append(b)
        if t not in parent:break
        path=[];v=t
        while v!=s:
            a=parent[v];path.append((a,v));v=a
        offer=min(g[a][b] for a,b in path)
        delivered+=offer
        for a,b in path:g[a][b]-=offer;g[b][a]+=offer
    assert delivered==sum(demands)
    return [[g[n+j].get(i,0) for j in range(m)] for i in range(n)]

def draw_schedule(edges,caps,targets):
    """Split capacities, then color a padded regular bipartite multigraph."""
    Q=lcm(*(x.denominator for x in targets))
    ints=[int(x*Q) for x in targets]
    f=integer_flow(edges,caps,ints,Q)
    n=len(edges); L=max(n,sum(caps))
    original=[[0]*L for _ in range(L)]
    slot_of=[]
    for j,s in enumerate(caps):
        assert sum(f[i][j] for i in range(n))<=s*Q
        left=s*Q
        start=len(slot_of)
        slot_of+= [j]*s
        for i in range(n):
            x=f[i][j]
            while x:
                filled=s*Q-left
                room=Q-filled%Q
                take=min(x,room)
                original[i][start+filled//Q]+=take
                x-=take;left-=take
    mult=[line[:] for line in original]
    row=[Q-sum(line) for line in mult]
    col=[Q-sum(line[k] for line in mult) for k in range(L)]
    for i,a in enumerate(row):
        for j,b in enumerate(col):
            q=min(a,b)
            mult[i][j]+=q;col[j]-=q;a-=q
        assert a==0
    draws=[]
    def assign(i,visited,match):
        for j,k in enumerate(mult[i]):
            if k and j not in visited:
                visited.add(j)
                if j not in match or assign(match[j],visited,match):
                    match[j]=i;return True
        return False
    for _ in range(Q):
        match={}
        for i in range(L):assert assign(i,set(),match)
        this=[]
        for j,i in match.items():
            mult[i][j]-=1
            if original[i][j]:
                original[i][j]-=1
                this.append((i,slot_of[j]))
        draws.append(sorted(this))
    assert not any(any(x) for x in original)
    for draw in draws:
        assert len(set(i for i,j in draw))==len(draw)
        assert all(j in edges[i] for i,j in draw)
        assert all(sum(g==j for _,g in draw)<=k for j,k in enumerate(caps))
    assert [F(sum(any(a==i for a,j in d) for d in draws),Q) for i in range(n)]==list(targets)
    return draws

def enumerate_draws(edges,caps):
    for a in product(*[[-1]+sorted(E) for E in edges]):
        if all(a.count(j)<=c for j,c in enumerate(caps)):
            yield a

def direct_lp(edges,caps,r):
    # Independent full distribution over legal deterministic allocations.
    import scipy.optimize as so
    draws=list(enumerate_draws(edges,caps))
    keep=[[-int(d[i]>=0) for d in draws]+[1] for i in range(len(edges))]
    x=so.linprog([0]*len(draws)+[-1],A_ub=keep,b_ub=[-float(t) for t in r],
       A_eq=[[1]*len(draws)+[0]],b_eq=[1],bounds=[(0,None)]*len(draws)+[(None,None)],
       method='highs')
    assert x.success,x.message
    return x.x[-1]

def show(edges,caps,r):
    eps,W=bound(edges,caps,r)
    if eps<=0:return dict(slack=str(eps),bottleneck=W)
    targets=[x+eps/2 for x in r]
    draws=draw_schedule(edges,caps,targets)
    return dict(slack=str(eps),bottleneck=W,targets=list(map(str,targets)),
             draws=draws)
def masks(edges,caps):
    return {tuple(i for i,x in enumerate(a) if x>=0)
            for a in enumerate_draws(edges,caps)}
def install_matching(T,edges,caps):
    return next((a for a in enumerate_draws(edges,caps)
                 if tuple(i for i,x in enumerate(a) if x>=0)==T),None)
def verify_subject_lottery(L,law,caps,r):
    for prob,T in L:
        assert prob>0 and all(install_matching(T,e,caps) is not None for e in law)
    assert sum(p for p,_ in L)==1
    margins=[sum((p for p,T in L if i in T),F(0)) for i in range(len(r))]
    assert all(a>b for a,b in zip(margins,r))
    return list(map(str,margins))
def timing_examples():
    e=([{0},{0},{1}],[{1},{0},{0}],[{0},{1},{0}])
    caps=[1,1]
    r=[F(49,100)]*3
    patterns=[masks(a,caps) for a in e]
    low=[F(1,2)]*3
    single=[
      [(F(1,2),(0,2)),(F(1,2),(1,))],
      [(F(1,2),(0,2)),(F(1,2),(1,))],
      [(F(1,2),(0,1)),(F(1,2),(2,))]
    ]
    for i,policy in enumerate(single):
        assert verify_subject_lottery(policy,[e[i]],caps,r)==list(map(str,low))
    common_two=verify_subject_lottery(single[0],e[:2],caps,r)
    M=set.intersection(*patterns)
    assert M=={(),(0,),(1,),(2,)}
    assert sum(r)>max(map(len,M))
    E=( [{0}], [{1}] )
    assert not set.intersection(*(a[0] for a in E))
    assert verify_subject_lottery([(F(1),(0,))],E,caps,[F(1,2)])==['1']
    return dict(known_role_marginals=list(map(str,low)),
                early_subject_allowed_under_two_roles=common_two,
                early_subject_common_sets_three=sorted(M),
                early_subject_total_threshold=str(sum(r)),
                late_assignment_single_subject_with_empty_edge_intersection=True)
def verify_coloring(n,edges):
    import scipy.optimize as so
    # Each role has a pair of subjects sharing a single slot; all other
    # subjects each have their own slot. Audit subjects lock in early.
    law=[]
    for a,b in edges:
        Z=[{j} for j in range(n)]
        Z[b]={a}
        law.append(masks(Z,[int(j!=b) for j in range(n)]))
    common=set.intersection(*law) if law else {(),*subsets(n)}
    indep={T for T in {(),*subsets(n)}
           if not any(a in T and b in T for a,b in edges)}
    assert common==indep
    S=sorted(indep)
    Y=[[-int(i in T) for T in S] for i in range(n)]
    coloring=so.linprog([1]*len(S),A_ub=Y,b_ub=[-1]*n,bounds=(0,None),method='highs')
    robust=so.linprog([0]*len(S)+[-1],A_ub=[v+[1] for v in Y],b_ub=[0]*n,
         A_eq=[[1]*len(S)+[0]],b_eq=[1],bounds=[(0,None)]*len(S)+[(None,None)],
         method='highs')
    assert coloring.success and robust.success
    assert abs(robust.x[-1]*coloring.fun-1)<1e-9
    return rounded_rational(coloring.fun),rounded_rational(robust.x[-1])

def rounded_rational(x):
    return str(F(float(x)).limit_denominator(1000))
def coloring_examples():
    edges=list(combinations(range(4),2))
    for keep in product((0,1),repeat=len(edges)):
        verify_coloring(4,[e for e,k in zip(edges,keep) if k])
    c5=[(0,1),(1,2),(2,3),(3,4),(4,0)]
    q,t=verify_coloring(5,c5);assert (q,t)==('5/2','2/5')
    return dict(four_vertex_graphs=2**len(edges),five_cycle_chi_fractional=q,
                five_cycle_maximum_common_inclusion=t)

def main():
    n=3;r=[F(3,5),F(3,5),F(2,5)]
    before=[{0},{0},{1}];after=[{0},{0,1},{1}]
    w=show(before,[1,1],r);x=show(after,[1,1],r)
    assert w["slack"]=="-1/10" and x["slack"]=="2/15"
    total=valid=0
    all_edges=[set(j for j in range(2) if mask>>j&1) for mask in range(4)]
    for edges in product(all_edges,repeat=n):
        for caps in ([1,1],[1,2],[2,1]):
            for q in ((F(0),F(1,2),F(3,4)),r,(F(9,10),F(1,5),F(1,5))):
                eps,_=bound(edges,caps,q)
                v=direct_lp(edges,caps,q)
                assert abs(float(eps)-v)<1e-9,(eps,v,edges,caps,q)
                if eps>0:
                    draw_schedule(edges,caps,[t+eps/2 for t in q]);valid+=1
                total+=1
    print(json.dumps(dict(before=w,after=x,lp_comparisons=total,decomposed=valid, timing=timing_examples(),graph= coloring_examples()),
                    indent=2,sort_keys=True))
if __name__=="__main__":main()
