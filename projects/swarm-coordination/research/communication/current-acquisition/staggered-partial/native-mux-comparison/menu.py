from itertools import combinations,product
from collections import Counter
from fractions import Fraction as F
import ast

PAIRS=((0,1),(0,3),(1,3),(2,3))
M=tuple(tuple(int(c==i)-int(c==j) for c in range(4))
        for i,j in (*PAIRS,*((i,-1) for i in range(4))))

def rows_of(path):
    tree=ast.parse(path.read_text())
    rows=[node for node in ast.walk(tree) if isinstance(node,ast.Assign) and
          any(isinstance(k,ast.Attribute) and k.attr=='A' for k in node.targets)]
    assert len(rows)==1
    a=rows[0].value.args[0].elts
    return tuple(tuple(-1 if isinstance(v,ast.UnaryOp) else 1 for v in row.elts) for row in a)

def rank(mat):
    a=[list(map(F,row)) for row in mat]
    n=0
    for col in range(4):
        k=next((i for i in range(n,len(a)) if a[i][col]),None)
        if k is None:continue
        a[n],a[k]=a[k],a[n]
        for i in range(n+1,len(a)):
            scale=a[i][col]/a[n][col]
            a[i]=[x-scale*y for x,y in zip(a[i],a[n])]
        n+=1
    return n

def verify(path):
    comb=[tuple(M[i] for i in c) for n in range(1,len(M)+1)
          for c in combinations(range(len(M)),n)]
    libs=[(x,rank(x)) for x in comb]
    front=[]
    for physical in rows_of(path):
        hist=Counter()
        for signs in product((-1,1),repeat=4):
            target=tuple(x*y for x,y in zip(physical,signs))
            value=min(len(x) for x,r in libs if rank(x+(target,))==r)
            formula=2 if target[0]==-target[1] and target[2]==-target[3] else 3 if len(set(target))==2 else 4
            assert value==formula
            hist[value]+=1
        front.append(dict(sorted(hist.items())))
    return dict(rows=rows_of(path),cases=len(comb)*16*len(front),frontier=front,
                late_sign_rank=min(len(x) for x,r in libs if r==4))
