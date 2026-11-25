from itertools import combinations
from math import isinf,inf,isclose
from random import Random
import json
import numpy as np
from scipy.optimize import linprog

# Each constraint x[b]-x[a] <= c with -1 denoting the fixed zero.
def outside(n,q,box,gaps,R):
    return [(a,b,c) for i,(l,u) in enumerate(box) for a,b,c in [(-1,i,u),(i,-1,-l)]] + [
        (i+1,i,-g) for i,g in enumerate(gaps)] + [(i,i+q,R) for i in range(n-q)]

def span(i,j,q,b,L,U):
    return [(-1,i+q-1,L+b),(i,-1,b-L),(-1,j+q-1,U+b),(j,-1,b-U)]+[
        (k,k+q,2*b) for k in range(i,j)]

def holds(e,x):
    at=lambda i:0 if i<0 else x[i]
    return all(at(j)-at(i)<=c+1e-8 for i,j,c in e)

def lp(A,B,v,cells,monotone=False,pins=None):
    n=len(A);m=len(cells);d=n*(m+1)+m
    assert m
    rows=[];rhs=[];eq=[];ev=[]
    def add(k,e):
        for i,j,c in e:
            r=np.zeros(d)
            if i>=0:r[k*n+i]-=1
            if j>=0:r[k*n+j]+=1
            rows.append(r);rhs.append(c)
    for l,e in enumerate(cells):
        add(l,e);add(l+1,e)
        for i in range(n):
            a=np.zeros(d);a[n*l+i]=-1;a[n*(l+1)+i]=1
            r=a.copy();r[n*(m+1)+l]=-v[i];rows.append(r);rhs.append(0)
            r=-a;r[n*(m+1)+l]=-v[i] if not monotone else 0
            rows.append(r);rhs.append(0)
    for l,E in [(0,A),(m,B)]:
        for i,x in enumerate(E):
            r=np.zeros(d);r[n*l+i]=1;eq.append(r);ev.append(x)
    for l,i,x in pins or []:
        r=np.zeros(d);r[n*l+i]=1;eq.append(r);ev.append(x)
    f=np.array([0.]*(n*(m+1))+[1.]*m)
    ans=linprog(f,A_ub=rows,b_ub=rhs,A_eq=eq,b_eq=ev,
                bounds=[(None,None)]*(n*(m+1))+[(0,None)]*m,method="highs")
    if ans.status==2:return inf,None
    assert ans.success,ans.message
    return ans.fun,[tuple(ans.x[i*n:i*n+n]) for i in range(m+1)]

def full(A,B,v,q,box,g,R,b,L,U):
    n=len(A);outer=outside(n,q,box,g,R)
    cells=[outer+span(i,j,q,b,L,U) for i in range(n-q+1) for j in range(i,n-q+1)]
    goal={i for i,e in enumerate(cells) if holds(e,B)}
    def adjacent(i,j):
        return holds(cells[i],A) and holds(cells[j],A) or intersection(cells[i],cells[j])
    def intersection(E,F):
        # Shortest-potential feasibility on the static common slice.
        pets=[0.]*(n+1)
        for _ in range(n+1):
            changed=False
            for x,y,z in E+F:
                if pets[y]>pets[x]+z+1e-8:pets[y]=pets[x]+z;changed=True
            if not changed:return True
        return False
    adj={i:[j for j in range(len(cells)) if i!=j and adjacent(i,j)] for i in range(len(cells))}
    best=inf
    def dfs(path):
        nonlocal best
        if path[-1] in goal:
            cost,_=lp(A,B,v,[cells[i] for i in path])
            best=min(best,cost)
            # Once the objective lies in this convex cell, continuing
            # out of it cannot improve over a chord directly to it.
            return
        for j in adj[path[-1]]:
            if j not in path:dfs(path+[j])
    for i,e in enumerate(cells):
        if holds(e,A):dfs([i])
    return best

def monotone(A,B,v,q,box,g,R,b,L,U):
    n=len(A)
    assert all(x<=y for x,y in zip(A,B))
    assert 0<U-L<min(g)
    outer=outside(n,q,box,g,R)
    marks=(L-b,U-b)
    state=[sum(x<s for x in A) for s in marks]
    seq=[]
    pins=[]
    def make():
        i,j=state
        if j>n-q:return None
        z=outer+span(i,j,q,b,L,U)
        for a,t in zip(state,marks):
            z += [(-1,h,t) if h<a else (h,-1,-t) for h in range(n)]
        return z
    seq.append(make())
    for i in reversed(range(n)):
        for j,t in enumerate(marks):
            if A[i]<t<=B[i]:
                state[j]-=1
                pins.append((len(seq),i,t))
                seq.append(make())
    assert state==[sum(x<s for x in B) for s in marks]
    if any(c is None for c in seq):return inf,None
    return lp(A,B,v,seq,monotone=True,pins=pins)

def point(A,B,v,q,box,g,R,b,L,U):
    assert L==U
    E=outside(len(A),q,box,g,R)
    cells=[E+span(i,i,q,b,L,U) for i in range(len(A)-q+1)]
    a=next(i for i,c in enumerate(cells) if holds(c,A))
    j=next(i for i,c in enumerate(cells) if holds(c,B))
    k=1 if a<=j else -1
    return lp(A,B,v,[cells[i] for i in range(a,j+k,k)])[0]

def exact(A,B,*params):
    M=tuple(map(min,A,B))
    t,_=monotone(M,A,*params)
    u,_=monotone(M,B,*params)
    return max(t,u)

def fixture(g):
    A=(-12,-3,g-3);B=(3-g,3,12)
    return A,B,(1,1,1),2,[(-15,15)]*3,[g]*2,8+g+1,4,-1,1

def main():
    for g,target in ((4,16),(5,inf)):
        a=fixture(g)
        assert isclose(full(*a),target) and isclose(exact(*a),target),(g,full(*a),exact(*a))
    rng=Random(849735)
    totals={'finite':0,'infinite':0,'incomparable':0}
    for _ in range(240):
        n=rng.randrange(3,5);q=rng.randrange(2,n);g=rng.choice([2,3,4])
        b=rng.randrange(2,7);L,U=-1,0
        R=rng.randrange(q*g,q*g+8);v=tuple(rng.randrange(1,4) for _ in range(n))
        box=[(-10,10)]*n
        E=outside(n,q,box,[g]*(n-1),R)
        cells=[E+span(i,j,q,b,L,U) for i in range(n-q+1) for j in range(i,n-q+1)]
        qs=[x for x in combinations(range(-8,9),n) if any(holds(e,x) for e in cells)]
        if not qs:continue
        A=rng.choice(qs);B=rng.choice(qs)
        p=v,q,box,[g]*(n-1),R,b,L,U
        a=full(A,B,*p);c=exact(A,B,*p)
        assert isclose(a,c,abs_tol=1e-7),(A,B,p,a,c)
        totals['infinite' if isinf(c) else 'finite']+=1
        if not all(a<=b for a,b in zip(A,B)) and not all(a>=b for a,b in zip(A,B)):
            totals['incomparable']+=1
    points=0
    for _ in range(120):
        g=rng.choice([1,2,3]);n=4;q=rng.randrange(2,4);b=rng.randrange(1,5)
        R=rng.randrange(q*g,q*g+5);v=tuple(rng.randrange(1,4) for j in range(n))
        box=[(-9,9)]*n
        p=v,q,box,[g]*(n-1),R,b,0,0
        outer=outside(n,q,box,[g]*(n-1),R)
        good=[x for x in combinations(range(-7,8),n)
              if any(holds(outer+span(i,i,q,b,0,0),x) for i in range(n-q+1))]
        if not good:continue
        A,B=(rng.choice(good),rng.choice(good))
        assert isclose(point(A,B,*p),full(A,B,*p),abs_tol=1e-7)
        points+=1
    totals['point_pairs']=points
    print(json.dumps(totals,sort_keys=True))
if __name__=='__main__':
    main()
