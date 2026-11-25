from fractions import Fraction as F
from itertools import product, combinations
from functools import lru_cache

zero,one=F(0),F(1)
def inspect(p,i,b):
 return sum(w for x,w in p.items() if x[i]==b)

def marginal(p, ids):
 out={}
 for x,w in p.items():
  key=tuple(x[i] for i in ids)
  out[key]=out.get(key,zero)+w
 return out

def frontier(points):
 # Minimize maximum of the two regrets over arbitrary randomized
 # pure policies: on the lower left edge or a single vertex.
 R=min(max(p) for p in points)
 for (a,b),(c,d) in combinations(points,2):
  if (a-b)*(c-d)<0:
   w=(d-c)/(a-b+d-c)
   assert zero<w<one
   R=min(R,w*a+(one-w)*c)
 return R

case_counts=leaves=costs=cheaper=0
for m in range(2,9):
 xs=list(product((0,1),repeat=m))
 def sign(x):return (-1)**(m-sum(x))
 for seed in range(1,8):
  weights={x:(17+13*(int(''.join(map(str,x)),2)+seed))%(m+seed+7)+1 for x in xs}
  z=sum(weights.values()); p={x:F(w,z) for x,w in weights.items()}
  L=-min(w for x,w in p.items() if sign(x)==1)
  H=min(w for x,w in p.items() if sign(x)==-1)
  assert L<0<H
  lo={x:w+L*sign(x) for x,w in p.items()}
  hi={x:w+H*sign(x) for x,w in p.items()}
  assert min(lo.values())==min(hi.values())==0
  assert sum(lo.values())==sum(hi.values())==1
  for i in range(m):
   a=tuple(j for j in range(m) if j!=i)
   assert marginal(lo,a)==marginal(hi,a)
   leaves+=2**(m-1)
  assert hi[xs[-1]]-lo[xs[-1]]==H-L
  case_counts+=1

pvals=tuple(F(i,10) for i in range(11))
for qlo,qhi,dlo,dhi,fp,fn in product(pvals,pvals,range(1,4),range(1,4),
                                  map(F,('0','0.1','0.25')),map(F,('0','0.1','0.4'))):
 if qhi<qlo:continue
 zlo=fp+(1-fp-fn)*qlo
 zhi=fp+(1-fp-fn)*qhi
 R0=F(dlo*dhi,dlo+dhi)
 cut=(zhi-zlo)*R0
 for c in {zero,cut/2,cut,cut+F(1,10)}:
  direct=[(zero,F(dhi)),(F(dlo),zero)]
  for u,v in product((0,1),repeat=2):
   direct.append((c+dlo*((1-zlo)*u+zlo*v),c+dhi*(1-(1-zhi)*u-zhi*v)))
  obs=(c+dlo*zlo,c+dhi*(1-zhi))
  R=frontier(direct)
  assert R==frontier(direct[:2]+[obs])
  assert (R<R0)==(c<cut)
  costs+=1
  cheaper+=R<R0
print(f'proper_marginal_families={case_counts} identical_maximal_audit_cells={leaves} one_run_regret_checks={costs} strict_value_cases={cheaper}')
assert frontier([(zero,one),(one,zero),(F(1,16),F(13,16))])==F(13,28)

full=0
for l,h in combinations(pvals,2):
 for x in ((l+h)/2,(2*l+h)/3,(l+2*h)/3):
  for fp,fn in product(map(F,('0','0.1','0.25')),map(F,('0','0.1','0.4'))):
   # Profit in the future episode is q-x, independently of the past
   # calibration episode under the same fixed law.
   dl,dh=x-l,h-x
   p=dh/(dl+dh)
   j=1-fp-fn
   z=lambda v: fp+j*v
   alpha=(dl*z(l)+dh*z(h))/(dl+dh)
   R=dl*dh/(dl+dh)
   k=(z(h)-z(l))*R/2
   r=min(p,1-p)/2
   a=p-r*alpha
   assert 0<=a<=1-r
   rate=lambda q:a+r*z(q)
   L=lambda q:(x-q)*rate(q)+r*k
   H=lambda q:(q-x)*(1-rate(q))+r*k
   # The low regret is decreasing from the left endpoint and high
   # regret increasing through the right endpoint, by concavity.
   assert -rate(l)+(x-l)*r*j<=0
   assert 1-rate(h)-(h-x)*r*j>=0
   assert L(l)==H(h)==R-r*k<R
   assert all(L(t)<=L(l) if t<=x else H(t)<=H(h)
              for t in [l+(h-l)*F(i,20) for i in range(21)])
   full+=1
print(f'full_interval_constructive_checks={full}')
