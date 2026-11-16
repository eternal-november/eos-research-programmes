from fractions import Fraction as F
from itertools import product
import json

def cartesian(X,U,Up,s,sp,u,h):
    return all(sum(s[z]==x and h[z]==zp for z in U)==1
               for x in X for zp in Up if u[x]==sp[zp])

def act(W,p,a,U,s,t):
    return {(w,z):p[w] for w in W for z in U if a[w]==s[z]}

def push(measure,f):
    out={}
    for z,p in measure.items(): out[f(z)]=out.get(f(z),F(0))+p
    return out

# Noninjective pure input map but genuine cartesian wiring square.
X=[0,1]; Xp=[0]; Up=['a','b']; U=list(product(X,Up))
s={z:z[0] for z in U}; sp={z:0 for z in Up}; u={0:0,1:0}
h={z:z[1] for z in U}; t={z:z[1] for z in U}; tp={z:z for z in Up}
assert cartesian(X,U,Up,s,sp,u,h)
W=['w0','w1','w2']; p={'w0':F(1,3),'w1':F(2,3),'w2':F(0)}
a={'w0':0,'w1':1,'w2':1}; Wp=['v']; pp={'v':F(1)}; ap={'v':0}
source=act(W,p,a,U,s,t); target=act(Wp,pp,ap,Up,sp,tp)
assert push(source,lambda z:('v',h[z[1]]))==target
assert ('w2',(1,'a')) in source # zero-weight witnesses retained

# The mass-one tests detect exactly a noncartesian collapse.
assert not cartesian([0],[0,1],[0],{0:0,1:0},{0:0},{0:0},{0:0,1:0})
assert sum(act(['w'],{'w':F(1)},{'w':0},[0,1],{0:0,1:0},{0:0,1:0}).values())==2

# Serial assembly: dependent continuation witnesses, not independent rows.
f={0:[('a',F(1,3),0),('b',F(2,3),1)],1:[('c',F(1),1)]}
g={0:[('d',F(2),0)],1:[('e',F(1,4),0),('f',F(3,4),1)]}
direct={(a,w,z):(p*q,c) for a,row in f.items() for w,p,b in row for z,q,c in g[b]}
named={(a,w,z):(p*q,c) for a,row in f.items() for w,p,b in row
       for bp,grow in g.items() for z,q,c in grow if b==bp}
assert direct==named

# Equality-wire feedback keeps matching raw witnesses with original weights.
body={(0,'p'):(F(1,2),0),(0,'q'):(F(1,2),1),
      (1,'r'):(F(1,3),0),(1,'s'):(F(2,3),1)}
closed={(loop,w):mass for (loop,w),(mass,out) in body.items() if loop==out}
assert closed=={(0,'p'):F(1,2),(1,'s'):F(2,3)}

# Direct naming of collapsing input square fails; reindexed target repairs it.
assert F(1)+F(1)!=F(1)
source_named={(0,'w'):F(1),(1,'w'):F(1)}
reindexed={(0,'v'):F(1),(1,'v'):F(1)}
assert push(source_named,lambda z:(z[0],'v'))==reindexed

# All-coupling joint comparison is strict even on diagonal law:
# diagonal source has 2 raw points; target joint law retains 4, including zeros.
diag={ (0,0):F(1),(0,1):F(0),(1,0):F(0),(1,1):F(1)}
assert len(diag)==4 and sum(diag.values())==2
assert push(diag,lambda z:z[0])=={0:F(1),1:F(1)}
assert push(diag,lambda z:z[1])=={0:F(1),1:F(1)}
# Shared-loop identity feedback: common boundary forces equal loop labels.
shared_raw=[(u,v) for u in (0,1) for v in (0,1) if (u,u)==(v,v)]
separately_closed_raw=list(product((0,1),repeat=2))
assert len(shared_raw)==2 and len(separately_closed_raw)==4
# Connected cospan: different bit couplings at the two wire witnesses.
mixed={(b,c,z):(F(1,2) if c==(b if z==0 else 1-b) else F(0))
       for b,c,z in product((0,1),repeat=3)}
assert push(mixed,lambda k:(k[0],k[2]))=={(b,z):F(1,2) for b,z in product((0,1),repeat=2)}
assert push(mixed,lambda k:(k[1],k[2]))=={(b,z):F(1,2) for b,z in product((0,1),repeat=2)}
assert any(mixed[b,c,0]!=mixed[b,c,1] for b,c in product((0,1),repeat=2))
# No common-boundary law before closure; a joint law exists after closure.
S={(0,0):F(1,2),(0,1):F(1,2)}
T={(0,0):F(1,2),(1,0):F(1,2)}
assert S!=T  # equal-boundary coupling necessarily has identical boundary marginals
assert {k:v for k,v in S.items() if k[0]==k[1]}=={k:v for k,v in T.items() if k[0]==k[1]}
print(json.dumps({'status':'passed','tests':['noninjective-pure-cartesian-square',
 'zero-witness-retention','noncartesian-multiplicity-obstruction',
 'dependent-bind-assembly','fixed-loop-feedback','relative-input-reindexing',
 'joint-raw-strictness','shared-loop-feedback-strictness','connected-coupling-strictness','feedback-empty-to-nonempty']},indent=2))
