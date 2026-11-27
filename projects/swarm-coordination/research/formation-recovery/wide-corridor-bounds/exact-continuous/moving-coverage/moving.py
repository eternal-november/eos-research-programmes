"""Finite spacetime extension: exact fixed-deadline checks for a moving covered interval."""
from fractions import Fraction as F
from itertools import product
import json
import numpy as np
from scipy.optimize import linprog
from certified import dot,rational
from exact_ref import outside,span
from projection import chord

def make(n,q,box,g,R,b,L,U,phases):
    # Phase is (left_time, right_time, slope, offset); shift=slope*t+offset.
    outer=outside(n,q,box,g,R)
    cells=[]
    for id,(l,r,s,k) in enumerate(phases):
        assert l<r and (not id or phases[id-1][1]==l)
        for i in range(n-q+1):
          for j in range(i,n-q+1):
            terms=[(a,b_,0,c) for a,b_,c in outer]
            for a,b_,c in span(i,j,q,b,L,U):
                w=int(a<0)-int(b_<0)
                terms.append((a,b_,-w*s,c+w*k))
            terms.extend(((-1,-1,1,r),(-1,-1,-1,-l)))
            cells.append((id,(i,j),terms))
    return cells

def here(spec,t,x):
    at=lambda i:0 if i<0 else x[i]
    return all(at(b)-at(a)+w*t<=c for a,b,w,c in spec)

def feasible(A,B,v,route,first,last):
    M=len(route);n=len(v);d=(n+1)*(M+1)
    rows=[];bounds=[]
    def add(terms,b):
        row=[F(0)]*d
        for i,v0 in terms:row[i]+=v0
        rows.append(tuple(row));bounds.append(b)
    def xi(j,i):return (n+1)*j+i
    def t(j):return xi(j,n)
    for j,(_,_,spec) in enumerate(route):
        for k in (j,j+1):
            for a,b,w,c in spec:
                x=[(t(k),w)]
                if a>=0:x.append((xi(k,a),-1))
                if b>=0:x.append((xi(k,b),1))
                add(x,c)
        add([(t(j),1),(t(j+1),-1)],0)
        for i,u in enumerate(v):
            for p in (-1,1):
                add([(xi(j,i),-p),(xi(j+1,i),p),(t(j),u),(t(j+1),-u)],0)
    for j,(pt,T) in ((0,(A,first)),(M,(B,last))):
        for i,x in enumerate((*pt,T)):
            for p in (-1,1):add([(xi(j,i),p)],p*x)
    mat=np.asarray(rows,dtype=float)
    ans=linprog([0]*d,A_ub=mat,b_ub=np.asarray(bounds,dtype=float),bounds=[(None,None)]*d,method="highs")
    if ans.status==2:
        alt=linprog([0]*len(rows),A_eq=np.vstack([mat.T,np.asarray(bounds,dtype=float)]),b_eq=[0]*d+[-1],
                    bounds=(0,None),method="highs")
        assert alt.success,alt.message
        y=rational(alt.x)
        assert all(b>=0 for b in y) and all(dot(col,y)==0 for col in zip(*rows)) and dot(bounds,y)==-1
        return None
    assert ans.success,ans.message
    x=rational(ans.x)
    assert all(dot(a,x)<=b for a,b in zip(rows,bounds)),("rational proposal rejected",ans.x)
    return [(x[t(j)],x[xi(j,0):t(j)]) for j in range(M+1)]

def execute(A,B,v,q,box,g,R,b,L,U,phases):
    cells=make(len(A),q,box,g,R,b,L,U,phases)
    ts=phases[0][0];tf=phases[-1][1]
    goals={j for j,(_,_,v0) in enumerate(cells) if here(v0,tf,B)}
    tests=0
    def dfs(seq):
        nonlocal tests
        j=seq[-1]
        if j in goals:
            route=[cells[k] for k in seq];tests+=1
            vals=feasible(A,B,v,route,ts,tf)
            if vals is not None:
                for (phase,_,spec),(u,x),(w,z) in zip(route,vals,vals[1:]):
                    _,_,s,k=phases[phase]
                    a=tuple(t-s*u-k for t in x);p=tuple(t-s*w-k for t in z)
                    assert here(spec,u,x) and here(spec,w,z)
                    assert chord(a,p,q,b,L,U)
                return tuple(vals)
            return None
        for k,(p,_,_) in enumerate(cells):
            if k not in seq and cells[j][0]<=p<=cells[j][0]+1:
                r=dfs([*seq,k])
                if r is not None:return r
        return None
    for j,(_,_,E) in enumerate(cells):
        if here(E,ts,A):
            r=dfs([j])
            if r is not None:return r,tests
    return None,tests

def check_formula(h):
    c=2 if h<=2 else 4/h
    cuts=sorted({F(0),c,F(2),4-c,F(4)})
    def pos(t):return F(0),4+max(0,min(t,4-t)-c)
    def offset(t):return h*min(t,4-t)/2
    assert pos(F(0))==pos(F(4))==(0,4)
    for u,v in zip(cuts,cuts[1:]):
        a,b=pos(u),pos(v)
        assert 1<=a[1]-a[0]<=6 and 1<=b[1]-b[0]<=6
        assert abs(a[1]-b[1])<=v-u
        assert chord(tuple(x-offset(u) for x in a),tuple(x-offset(v) for x in b),1,2,0,1)
def main():
    tests=0;yes=[]
    peaks=sorted({F(i,2) for i in range(21)} | {F(637,100),F(638,100),F(51,8),F(509,80)})
    for h in peaks:
        phases=((0,2,h/2,0),(2,4,-h/2,2*h))
        got,n=execute((0,4),(0,4),(0,1),1,[(-8,15)]*2,[1],6,2,0,1,phases)
        analytic=h<=2 or h*h-7*h+4<=0
        assert (got is not None)==analytic,(h,got)
        if h==F(13,2):assert h<=7 and got is None
        tests+=n
        if got is not None:
            check_formula(h)
            yes.append(str(h))
    print(json.dumps({"fixture_peak_values":len(peaks),"feasible":len(yes),"max_tested_feasible":yes[-1],"certified_paths":tests},sort_keys=True))
if __name__=="__main__":
    main()
