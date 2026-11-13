"""Exact finite checks supporting, not replacing, representation proofs."""
from fractions import Fraction as F
from itertools import product

def law(weights, outputs):
    ans={}
    for p,b in zip(weights,outputs): ans[b]=ans.get(b,F(0))+p
    return {b:p for b,p in ans.items() if p}
def arrow(p,h,q,k,r):
    return all(h[x]==k[r[x]] for x in range(len(p))) and all(sum((p[x] for x in range(len(p)) if r[x]==y),F(0))==q[y] for y in range(len(q)))
def exists(p,h,q,k):
    return any(arrow(p,h,q,k,r) for r in product(range(len(q)),repeat=len(p)))
p=[F(1,2),F(1,2)]; h=['b','b']; q=[F(1)]; k=['b']
assert arrow(p,h,p,h,[0,1]) and arrow(p,h,p,h,[1,0])
assert not exists(q,k,p,h) and exists(p,h,q,k)
assert law(p,h)==law(q,k)
assert not exists([F(1),F(0)],['b0','b1'],[F(1)],['b0'])
cases=0
for n in range(1,5):
 for mass in product(range(4), repeat=n):
  total=sum(mass)
  if not total: continue
  ps=[F(m,total) for m in mass]
  for hs in product(range(2),repeat=n):
   # continuation depends on first output, nonuniform and with zero witness
   cont={0:([F(1,3),F(2,3)],[0,1]),1:([F(0),F(1,4),F(3,4)],[2,0,2])}
   ws=[]; outs=[]
   for px,b in zip(ps,hs):
    for py,c in zip(*cont[b]):ws.append(px*py);outs.append(c)
   result=law(ws,outs); expected={}
   for b,pb in law(ps,hs).items():
    for c,pc in law(*cont[b]).items():expected[c]=expected.get(c,F(0))+pb*pc
   assert result==expected
   for z in ['red','blue']:
    assert law(ps,[(z,b) for b in hs])=={(z,b):pb for b,pb in law(ps,hs).items()}
   cases+=1
print(f'PASS: {cases} exact composition cases; nonfaithfulness/nonfullness, raw-zero obstruction, and nonunit frames')

# Full List arity shadow: independently sample each addressed occurrence,
# including repeated outputs and nullary initial lists, then concatenate.
def list_compose_history(ps, hs, continuation):
    weights=[];outputs=[]
    for p,bs in zip(ps,hs):
        alternatives=[list(zip(*continuation[b])) for b in bs]
        for picked in product(*alternatives):
            weight=p; out=()
            for q,cs in picked: weight*=q;out+=cs
            weights.append(weight);outputs.append(out)
    return law(weights,outputs)
def list_compose_laws(k,l):
    result={}
    for bs,p in k.items():
        for picked in product(*(list(l[b].items()) for b in bs)):
            weight=p; out=()
            for cs,q in picked:weight*=q;out+=cs
            result[out]=result.get(out,F(0))+weight
    return {x:p for x,p in result.items() if p}
cont={0:([F(1,2),F(1,2)],[(),(0,1)]),1:([F(0),F(1,3),F(2,3)],[(7,),(1,),(0,)])}
l={b:law(*data) for b,data in cont.items()}
listcases=0
for hs in product([(),(0,),(1,),(0,0),(0,1),(1,0)],repeat=3):
    ps=[F(0),F(1,3),F(2,3)]
    assert list_compose_history(ps,hs,cont)==list_compose_laws(law(ps,hs),l)
    listcases+=1
print(f'PASS: {listcases} exact List-quotient cases, including repeated occurrences, nullary lists and zero witnesses')
