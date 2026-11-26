from itertools import product
from functools import lru_cache

W=((0,0),(0,1),(1,1))
INF=10**5
SHAPES=((0,0,0),(0,None,None),(None,0,None),(None,None,0),
        (0,0,None),(0,-1,None),(-1,0,None),
        (None,0,0),(None,0,-1),(None,-1,0))

def state(shape,M,V,end,P):
    return (tuple(-1 if k is None or M+k<0 else M+k for k in shape),V,end,P)

def normalize(key):
    b,V,end,P=key
    M=max(b)
    return M,(tuple(x-M if x>=0 else None for x in b),V,end,P)

def terminal(key):
    b,V,end,P=key
    return all(any((g==0 and end>=0 and V==v) or
                 (P>>(2*g+v)&1 and all(W[j][g]==v for j,x in enumerate(b) if x>=0))
                 for v in (0,1)) for g in (0,1))

def problem(h,complete):
    @lru_cache(None)
    def spread(b):
        return tuple(max([-1]+[x-(int(i!=j) if complete else abs(i-j))
                               for i,x in enumerate(b) if x>=0]) for j in range(3))
    def nexts(key):
        b,V,end,P=key
        alive=(V,end-1) if end>0 else (-1,-1)
        ext=spread(b)
        actions=[]
        for g,v in product((0,1),repeat=2):
            branches=[]
            for c in (0,1):
                xx=tuple(x if (W[j][g]==v)==bool(c) else -1 for j,x in enumerate(ext))
                if max(xx)<0:continue
                T=P|(1<<(2*g+v)) if c else P
                R=[(xx,*alive,T)]
                if g==0 and c:R.append((xx,v,h,T))
                branches.append(R)
            actions.append(branches)
        return actions
    return nexts

def compute(h,complete,N):
    nexts=problem(h,complete)
    meta=[(-1,-1)]+list(product((0,1),range(h+1)))
    # Extra metadata states that could not arise physically are harmless;
    # the transition closure covers them too.
    data={state(S,M,V,end,P) for S,M,(V,end),P in product(
          SHAPES,range(N+1),meta,range(16))}
    term={k for k in data if terminal(k)}
    n={k:nexts(k) for k in data-term}
    assert all(a in data for branches in n.values() for action in branches for group in action for a in group)
    table=dict.fromkeys(term,0)
    for bound in range(1,8*(N+1)+1):
        done=[k for k,ac in n.items() if any(all(any(a in table for a in group) for group in branches) for branches in ac)]
        for k in done:
            table[k]=bound
            del n[k]
        if not n:break
    assert not n
    return table,nexts,meta

def cert(h,complete,K,N):
    D,T,meta=compute(h,complete,N)
    sig=[(sh,V,end,P) for sh,(V,end),P in product(SHAPES,meta,range(16))]
    def value(M,sg):
        return D[state(sg[0],M,*sg[1:])]
    affine={(sg,r):(value(K+r+4,sg)-value(K+r,sg),value(K+r,sg))
            for sg in sig for r in range(4)}
    assert all(a in range(5) for a,b in affine.values()), sorted(set(a for a,b in affine.values()))
    def pred(k):
        M,sg=normalize(k)
        if M<K:
            return D[k]
        q,r=divmod(M-K,4)
        a,b=affine[(sg,r)]
        return a*q+b
    for m in range(K,N+1):
        for sg in sig:
            assert pred(state(sg[0],m,*sg[1:]))==value(m,sg), (h,complete,m,sg,[value(k,sg) for k in range(N+1)])
    # Above K+2 all child budgets are >=K and operations pull the same
    # affine functions. At most one relative slope break can occur per pair.
    for m in range(N+1):
        for sg in sig:
            k=state(sg[0],m,*sg[1:])
            f=0 if terminal(k) else 1+min(max(min(map(pred,group)) for group in act) for act in T(k))
            assert f==pred(k)
    symbolic=0
    for sg,r in product(sig,range(4)):
        m=K+r
        while m<K+2:m+=4
        k=state(sg[0],m,*sg[1:])
        v=pred(k)
        qv=pred(state(sg[0],m+4,*sg[1:]))
        if terminal(k):
            assert v==qv==0
            continue
        assert v>0 and qv>=v
        acts=[]
        for a in T(k):
            rows=[]
            for g in a:
                line=[]
                for z in g:
                    M,sig_z=normalize(z)
                    assert M>=K and m-M<=2
                    az,bz=affine[(sig_z,(M-K)%4)]
                    line.append((az,pred(z)))
                rows.append(line)
            acts.append(rows)
        lines=[(v[0]+0,v[1]+1) for a in acts for g in a for v in g]
        lines.append((qv-v,v))
        bound=max(abs(a[1]-b[1]) for a in lines for b in lines)+3
        for q in range(bound+1):
            b=1+min(max(min(az*q+bz for az,bz in g) for g in a) for a in acts)
            assert b==v+(qv-v)*q
            symbolic+=1
    return affine,D,T,meta,symbolic

if __name__=="__main__":
    import json
    out={}
    for complete in (False,True):
        K,N=13,24
        af,D,_,_,sym=cert(1,complete,K,N)
        sg=((0,0,0),-1,-1,0)
        values=[D[state(sg[0],m,*sg[1:])] for m in range(N+1)]
        assert values==[3]+[m+(4 if complete else 3) for m in range(1,N+1)]
        assert [af[(sg,r)] for r in range(4)]==[(4,K+r+(4 if complete else 3)) for r in range(4)]
        out["complete" if complete else "path"]=dict(
          finite_states=len(D),tail_scalar_equations_checked=sym,
          initial_read_budgets_zero_to_ten=values[:11],
          residue_period=4,affine_tail_threshold=K)
    print(json.dumps(out,indent=2))
