"""Bounded exact-integer diagnostics, not a proof of the universal classification."""
from itertools import product
from pathlib import Path
import json


def functions(n,m):
    return list(product(range(m),repeat=n))


def couplings(P,Q):
    # P,Q list (raw boundary, integer mass). Retain all compatible zero points.
    allowed=[(i,j) for i,(x,p) in enumerate(P) for j,(y,q) in enumerate(Q) if x==y]
    rows=[[(i,j) for ii,j in allowed if ii==i] for i in range(len(P))]
    result=[]
    def allocate(i,remaining,chosen):
        if i==len(P):
            if not any(remaining):result.append(tuple(chosen.get(z,0) for z in allowed))
            return
        cells=rows[i]
        def distribute(k,left,rem,new):
            if k==len(cells):
                if left==0: allocate(i+1,rem,chosen|new)
                return
            z=cells[k];j=z[1]
            for n in range(min(left,rem[j])+1):
                nxt=list(rem);nxt[j]-=n
                distribute(k+1,left-n,nxt,new|{z:n})
        distribute(0,P[i][1],remaining,{})
    allocate(0,[m for _,m in Q],{})
    return allowed,result


def act(P,s,t):
    keys=[(i,u) for i,(x,m) in enumerate(P) for u in range(len(s)) if s[u]==x]
    return keys,[(t[u],P[i][1]) for i,u in keys]


def product_comparison_iso(P,Q,s,t):
    source_raw,source_laws=couplings(P,Q)
    pk,AP=act(P,s,t);qk,AQ=act(Q,s,t)
    target_raw,target_laws=couplings(AP,AQ)
    source_acted=[(z,u) for z in source_raw for u in range(len(s)) if P[z[0]][0]==s[u]]
    image_raw=[(pk.index((z[0],u)),qk.index((z[1],u))) for z,u in source_acted]
    if source_laws and set(image_raw)!=set(target_raw):return False
    images=[]
    for law in source_laws:
        base=dict(zip(source_raw,law));image=dict.fromkeys(target_raw,0)
        for (z,u),out in zip(source_acted,image_raw):image[out]+=base[z]
        images.append(tuple(image[z] for z in target_raw))
    return len(set(images))==len(images) and set(images)==set(target_laws)


spans=pair_tests=0
for nx,ny,nu in product(range(3),repeat=3):
    for s in functions(nu,nx):
        for t in functions(nu,ny):
            spans+=1
            states=[[]]
            for x in range(nx):
                states += [[(x,2)],[(x,4)],[(x,1),(x,1)]]
            observed=True
            for P,Q in product(states,repeat=2):
                pair_tests+=1
                observed &= product_comparison_iso(P,Q,s,t)
            s_bij=(nu==nx and len(set(s))==nx)
            t_inj=(len(set(t))==nu)
            assert observed==(s_bij and t_inj),(nx,ny,nu,s,t,observed)
            # Raw t plus index functions on the {0,1}-weight cube detect terminal cases.
            t_bij=(nu==ny and len(set(t))==ny)
            terminal=False
            if t_bij:
                images=[]
                for mu in product((0,1),repeat=nx):
                    out=[0]*ny
                    for u,x in enumerate(s):out[t[u]]+=mu[x]
                    images.append(tuple(out))
                terminal=(len(set(images))==len(images) and set(images)==set(product((0,1),repeat=ny)))
            assert terminal==(s_bij and t_bij),(nx,ny,nu,s,t)

report={'status':'passed','scope':'all finite spans with X,Y,U cardinalities at most 2; listed native singleton/fair/empty test states and integer coupling grids only','spans':spans,'binary_pair_diagnostics':pair_tests,'terminal_weight_grid':[0,1],'note':'Universal real-weight/all-system statements rely on written proofs, not these bounded diagnostics.'}
print(json.dumps(report,indent=2))
