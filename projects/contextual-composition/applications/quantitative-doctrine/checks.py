from fractions import Fraction as F
from itertools import combinations, product
import json

def solve_columns(cols, target):
    # Exact overdetermined system; accept only independent columns.
    a=[list(row)+[b] for row,b in zip(zip(*cols),target)]
    n=len(cols); r=0
    for j in range(n):
        p=next((i for i in range(r,len(a)) if a[i][j]),None)
        if p is None:return None
        a[r],a[p]=a[p],a[r]; z=a[r][j]; a[r]=[v/z for v in a[r]]
        for i in range(len(a)):
            if i!=r:
                z=a[i][j]; a[i]=[x-z*y for x,y in zip(a[i],a[r])]
        r+=1
    if any(not any(row[:n]) and row[n] for row in a):return None
    return [a[i][-1] for i in range(n)]
def inside(point, vertices):
    # Affine Caratheodory certificate with independent augmented columns.
    for k in range(1,min(len(vertices),len(point)+1)+1):
        for vv in combinations(vertices,k):
            w=solve_columns([tuple(v)+(F(1),) for v in vv],tuple(point)+(F(1),))
            if w is not None and min(w)>=0:return True
    return False
def hull_equal(v,w):return all(inside(x,w) for x in v) and all(inside(x,v) for x in w)
S=('L','R','U','G')
ps={'L':[F(1,4),F(3,4)],'R':[F(1,4),F(1,2),F(3,4)],'U':[F(1,2),F(3,4)]}
K={s:{'request':[{s:1-p,'G':p} for p in ps[s]]} for s in ps}
K['G']={'execute':[{'G':F(1)}]}
def projected(s,a,P):return [tuple(sum((mu.get(t,F(0)) for t in block),F(0)) for block in P) for mu in K[s][a]]
def equivalent(s,t,P):return K[s].keys()==K[t].keys() and all(hull_equal(projected(s,a,P),projected(t,a,P)) for a in K[s])
def refine(P):
    out=[]
    for block in P:
        groups=[]
        for s in block:
            for group in groups:
                if equivalent(s,group[0],P):group.append(s);break
            else:groups.append([s])
        out.extend(groups)
    return out
P=[['L','R','U'],['G']]; history=[P]
while True:
    Q=refine(P)
    if Q==P:break
    P=Q;history.append(P)
assert P==[['L','R'],['U'],['G']]
assert projected('L','request',P)!=projected('R','request',P)
assert hull_equal(projected('L','request',P),projected('R','request',P))
assert not hull_equal(projected('L','request',P),projected('U','request',P))
# Must-safety loses the quantitative distinction on initial public partition.
P0=history[0]
for safe in product([False,True],repeat=2):
    must=[]
    for s in ['L','R','U']:
        must.append(all(all(safe[i] or p==0 for i,p in enumerate(v)) for v in projected(s,'request',P0)))
    assert len(set(must))==1
# Exact adaptive request-until-granted (otherwise stop at budget) values.
v={s:F(s=='G') for s in S}; vals=[]
for h in range(1,7):
    v={s:(F(1) if s=='G' else min(sum(p*v[t] for t,p in mu.items()) for mu in K[s]['request'])) for s in S}
    assert v['L']==v['R']==1-F(3,4)**h
    assert v['U']==1-F(1,2)**h
    vals.append({s:str(x) for s,x in v.items()})
# Convex-membership tests not confined to collinear examples.
tri=[(F(0),F(0)),(F(1),F(0)),(F(0),F(1))]
assert inside((F(1,3),F(1,3)),tri)
assert not inside((F(3,4),F(3,4)),tri)
# Availability must be a separate condition even if kernels coincide.
old=K['R'];K['R']={'other':old['request']}
assert not equivalent('L','R',P)
K['R']=old
print(json.dumps({'status':'PASS','partition_history':history,'two_request_success':vals[1],'six_horizon_values':vals,'scope':'finite exact checks; no formal proof checker'},indent=2))
