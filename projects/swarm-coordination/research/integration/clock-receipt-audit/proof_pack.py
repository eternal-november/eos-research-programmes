"""Generate/check certificates for joint source and recipient chronology."""
from cut import *
from itertools import product
import json

def negative_cycle(n,arcs):
    d=[0]*n;parents=[None]*n
    for _ in range(n):
        end=None
        for k,(u,v,b) in enumerate(arcs):
            if d[u]+b<d[v]:d[v]=d[u]+b;parents[v]=k;end=v
        if end is None:return None
    x=end
    for _ in range(n): x=arcs[parents[x]][0]
    y=x; s=[]
    while True:
        k=parents[y];s.append(k);y=arcs[k][0]
        if y==x:break
    assert sum(arcs[k][2] for k in s)<0
    return s[::-1]

def certify(case,arcs,routes,n=9):
    example=vertex_witness(n,arcs)
    assert example is not None
    for choices in product(*(range(len(z)) for z in routes)):
        zz=tuple(arcs)+tuple(neg(z[i]) for z,i in zip(routes,choices))
        c=negative_cycle(n,zz)
        if c is None:
            w=vertex_witness(n,zz)
            assert w is not None
            return dict(n=n,case=case,base=arcs,routes=routes,schedule=w)
    slices=[]
    for choices in product(*(range(len(z)) for z in routes)):
        zz=tuple(arcs)+tuple(neg(z[i]) for z,i in zip(routes,choices))
        slices.append((choices,negative_cycle(n,zz)))
    return dict(n=n,case=case,base=arcs,routes=routes,cycles=slices,base_example=example)

def main():
    Y,P,R=specimen(1)
    Z,_,V=specimen(2)
    # Preserve each projection and detach B's source offset from A's.
    D=tuple((9 if u==1 and v==5 else u,9 if v==1 and u==5 else v,c)
            for u,v,c in Y)+interval(0,9,-1,1)
    cases=(certify('common-clock capture',Y,P),
           certify('detached-clock capture',D,P,10),
           certify('reported at 1',Y,R),
           certify('reported at 2',Z,V),
           certify('B receipt only at 2',Z,(V[1],)))
    with open('certificates.json','w') as f:
        f.write(json.dumps(cases,sort_keys=True,separators=(',',':'))+'\n')
if __name__=='__main__':main()
