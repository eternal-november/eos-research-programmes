#!/usr/bin/env python3
"""Finite exact checks. Standard library only; no assertions disabled by -O."""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
import json
from pathlib import Path
import sys

def require(ok, message):
    if not ok: raise RuntimeError(message)
def mat(rows): return tuple(tuple(F(x) for x in row) for row in rows)
def tr(a): return tuple(zip(*a))
def mul(a,b):
    require(len(a[0])==len(b),'matrix dimensions')
    return tuple(tuple(sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)) for row in a)
def support(a): return tuple(tuple(bool(x) for x in row) for row in a)
def bmul(a,b): return tuple(tuple(any(x and y for x,y in zip(row,col)) for col in zip(*b)) for row in a)
def total(a): return sum(map(sum,a),F(0))
def stochastic(a): return all(all(x>=0 for x in row) and sum(row)==1 for row in a)
def rank2(a):
    require(len(a)==len(a[0])==2,'rank2 domain')
    return 0 if not any(map(any,a)) else 1 if a[0][0]*a[1][1]==a[0][1]*a[1][0] else 2
def brank(a):
    m,n=len(a),len(a[0]); target=sum(1<<(i*n+j) for i in range(m) for j in range(n) if a[i][j])
    rectangles=[]
    for rs in range(1,1<<m):
      for cs in range(1,1<<n):
        mask=sum(1<<(i*n+j) for i in range(m) for j in range(n) if rs>>i&1 and cs>>j&1)
        if mask&target==mask: rectangles.append(mask)
    @lru_cache(None)
    def cover(left):
        if not left:return 0
        bit=left&-left
        return 1+min(cover(left&~r) for r in rectangles if r&bit)
    return cover(target)
def bmats(m,n):
    return [tuple(tuple(bits[i*n+j] for j in range(n)) for i in range(m)) for bits in product((False,True),repeat=m*n)]
def native_check(a,b,q,r,w):
    require(stochastic(b) and stochastic(q),'normalized emissions and links')
    require(all(x>=0 for row in a for x in row) and total(a)==1,'root normalization')
    t=mul(a,b)
    require(mul(t,q)==r,'native observable law')
    require(tuple(map(sum,zip(*t)))==w,'native coarse marginal')
    emission=mul(b,q)
    require(stochastic(emission),'native second step normalization')
    return t
I=mat([[1,0],[0,1]]); P=mat([[0,1],[1,0]]); collapse=mat([[1],[1]])
Q=mat([[F(4,5),F(1,5)],[F(1,5),F(4,5)]]); w=(F(1,2),F(1,2))
QINV=mat([[F(4,3),F(-1,3)],[F(-1,3),F(4,3)]])
require(mul(Q,QINV)==I,'inverse')
cases=[('independent',F(1,4),F(1,4)),('middle',F(37,100),F(13,100)),('boundary',F(2,5),F(1,10)),('sharp',F(9,20),F(1,20))]
expected_t=[mat([[F(1,4)]*2]*2),mat([[F(9,20),F(1,20)],[F(1,20),F(9,20)]]),mat([[F(1,2),0],[0,F(1,2)]]),mat([[F(7,12),F(-1,12)],[F(-1,12),F(7,12)]])]
results={}; positive=[]
for idx,(name,d,o) in enumerate(cases):
    r=mat([[d,o],[o,d]]); t=mul(r,QINV)
    require(t==expected_t[idx],'fixed control solution '+name)
    require(mul(t,Q)==r and tuple(map(sum,zip(*t)))==w,'linear equations '+name)
    require(all(map(all,support(r))) and all(map(all,support(Q))),'common Boolean data')
    feasible=all(x>=0 for row in t for x in row)
    if feasible:
        a,b=(mat([[F(1,2)],[F(1,2)]]),mat([[F(1,2),F(1,2)]])) if name=='independent' else (t,I)
        require(native_check(a,b,Q,r,w)==t,'native constructor')
        positive.append((name,r,t,a,b))
    results[name]={'T':[[str(x) for x in row] for row in t], 'feasible':feasible,'full_support_feasible':feasible and all(map(all,support(t))), 'native_states':2+rank2(t) if feasible else None}
u=mat([[-1,0],[0,-1]]); sharp=mat([[F(9,20),F(1,20)],[F(1,20),F(9,20)]])
lhs=sum(u[j][i]*sharp[j][i] for j in range(2) for i in range(2)); rhs=sum(w[s]*min(sum(u[j][i]*Q[s][i] for i in range(2)) for j in range(2)) for s in range(2))
require(lhs==F(-9,10) and rhs==F(-4,5) and lhs<rhs,'sharp dual certificate')
# The Boolean criterion uses the largest compatible relation, not a rank guess.
rowtotal=[a for a in bmats(2,2) if all(map(any,a))]
feasible_count=0; opt_hist={}; witnesses_count=0
for q in rowtotal:
 for r in rowtotal:
    maximal=tuple(tuple(all(not q[s][i] or r[j][i] for i in range(2)) for s in range(2)) for j in range(2))
    criterion=bmul(maximal,q)==r and all(map(any,zip(*maximal)))
    witnesses=[t for t in bmats(2,2) if bmul(t,q)==r and all(map(any,zip(*t)))]
    require(criterion==bool(witnesses),'Boolean criterion')
    if witnesses:
        feasible_count+=1; witnesses_count+=len(witnesses)
        optimum=min(map(brank,witnesses)); opt_hist[str(optimum)]=opt_hist.get(str(optimum),0)+1
        # Independent direct factor enumeration validates rectangle cover rank.
        for t in witnesses:
            direct=next(k for k in (1,2) if any(bmul(a,b)==t for a in bmats(2,k) for b in bmats(k,2)))
            require(brank(t)==direct,'rectangle factor equivalence')
# Comparison square: U on announcements; F on states; G on outputs.
def compare(r,t,a,b,q,w,u,f,g,qp):
    require(stochastic(u) and stochastic(f) and stochastic(g) and stochastic(qp),'comparison normalization')
    require(mul(q,g)==mul(f,qp),'comparison input square')
    wp=mul((w,),f)[0]; rp=mul(mul(tr(u),r),g); tp=mul(mul(tr(u),t),f)
    ap=mul(tr(u),a); bp=mul(b,f)
    require(native_check(ap,bp,qp,rp,wp)==tp,'comparison factor transport')
    require(support(tp)==bmul(bmul(tr(support(u)),support(t)),support(f)),'support transport')
    require(brank(support(tp))<=brank(support(t)),'Boolean rank monotonicity')
    return rp,tp,ap,bp,qp,wp
comparison_count=0; sequential_count=0
for name,r,t,a,b in positive:
 for u in (I,P,collapse,mat([[F(3,4),F(1,4)],[F(1,4),F(3,4)]])):
  for f in (I,P):
   for g in (I,P,collapse,mat([[F(2,3),F(1,3)],[F(1,3),F(2,3)]])):
    qp=mul(mul(tr(f),Q),g)
    out=compare(r,t,a,b,Q,w,u,f,g,qp); comparison_count+=1
    require(len(out[2][0])==len(a[0]),'factor state budget retained')
    # A second state permutation and output/announcement collapse.
    u2=mat([[1] for _ in range(len(out[0]))]); f2=P; g2=mat([[1] for _ in range(len(qp[0]))]); qpp=mul(mul(tr(f2),qp),g2)
    out2=compare(*out[:4],out[4],out[5],u2,f2,g2,qpp)
    direct=compare(r,t,a,b,Q,w,mul(u,u2),mul(f,f2),mul(g,g2),qpp)
    require(out2==direct,'strict sequential coherence')
    sequential_count+=1
state_collapse_count=0
for name,r,t,a,b in positive:
    compare(r,t,a,b,Q,w,I,collapse,collapse,mat([[1]]))
    state_collapse_count+=1
# A noninvertible factorization morphism merges two identical latent emissions.
arrow_source_a=mat([[F(1,4),F(1,4)],[F(1,4),F(1,4)]])
arrow_source_b=mat([[F(1,2),F(1,2)],[F(1,2),F(1,2)]])
arrow_target_a=mat([[F(1,2)],[F(1,2)]]); arrow_target_b=mat([[F(1,2),F(1,2)]])
c=collapse
require(mul(arrow_source_a,c)==arrow_target_a and mul(c,arrow_target_b)==arrow_source_b,'noninvertible factor arrow')
arrow_checks=0
for u in (I,P,collapse):
 for f in (I,P,collapse):
    require(mul(mul(tr(u),arrow_source_a),c)==mul(tr(u),arrow_target_a),'arrow A naturality')
    require(mul(c,mul(arrow_target_b,f))==mul(arrow_source_b,f),'arrow B naturality')
    require(bmul(support(c),support(mul(arrow_target_b,f)))==support(mul(arrow_source_b,f)),'support on arrow')
    arrow_checks+=1
summary={'factor_arrow_transport_checks':arrow_checks,'state_collapse_comparisons' :state_collapse_count,'fixed_controls':results,'sharp_dual':{'lhs':str(lhs),'rhs':str(rhs)},'boolean_exhaustive':{'input_pairs':len(rowtotal)**2,'feasible':feasible_count,'infeasible':len(rowtotal)**2-feasible_count,'feasible_witnesses':witnesses_count,'optimal_factor_rank_histogram':opt_hist},'comparison_squares':comparison_count,'sequential_comparisons':sequential_count}
text=json.dumps(summary,indent=2,sort_keys=True)+'\n'
if '--write-expected' in sys.argv: Path(__file__).with_name('expected_results.json').write_text(text)
else:
    expected=Path(__file__).with_name('expected_results.json').read_text()
    require(text==expected,'expected results mismatch')
print(text,end='')
