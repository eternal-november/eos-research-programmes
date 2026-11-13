from fractions import Fraction as F
from collections import defaultdict
H={(0,'*'):F(1,2),(1,0):F(1,4),(1,1):F(1,4)}
ret={(x,y,y):p for (x,y),p in H.items()}
new={}
for (x,y),p in H.items():
 for z,r in ({'*':F(1)} if x==0 else {0:F(1,2),1:F(1,2)}).items():
  new[x,y,z]=p*r

def push(d,f):
 o=defaultdict(F)
 for k,v in d.items():o[f(k)]+=v
 return dict(o)
def tv(a,b):return sum((abs(a.get(k,F())-b.get(k,F())) for k in a.keys()|b.keys()),F())/2
assert sum(ret.values())==sum(new.values())==1
assert push(ret,lambda t:(t[0],t[2]))==push(new,lambda t:(t[0],t[2]))==H
assert tv(ret,new)==F(1,4)
assert sum(p for (x,y,z),p in new.items() if y==z)==F(3,4)
assert sum(p for (x,y,z),p in ret.items() if y==z)==1
assert push(new,lambda t:(t[0],t[1]))==H
assert push(H,lambda t:t[0])=={0:F(1,2),1:F(1,2)}
shared={(0,0):F(1,2),(1,1):F(1,2)}
independent={(x,y):F(1,4) for x in (0,1) for y in (0,1)}
assert tv(shared,independent)==F(1,2)
assert tv({(y,z):2*p for (x,y,z),p in ret.items() if x==1}, {(y,z):2*p for (x,y,z),p in new.items() if x==1})==F(1,2)
assert tv({0:F(1)},{0:F(1,2),1:F(1,2)})==F(1,2)
print('All 10 exact assertions passed.')
for name,d in [('retained',ret),('resampled',new)]:
 print(name, {str(k):str(v) for k,v in d.items()})
print('Joint total variation:',tv(ret,new))
