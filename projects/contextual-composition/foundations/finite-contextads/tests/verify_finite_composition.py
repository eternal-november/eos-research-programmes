from fractions import Fraction as F
from collections import defaultdict
from itertools import product

def norm(d):
    return {k:v for k,v in d.items() if v}

def push(p, f):
    q=defaultdict(F)
    for x,v in p.items(): q[f(x)]+=v
    return norm(q)

def compose(k, l):
    out={}
    for a,ka in k.items():
        acc=defaultdict(F)
        for b,p in ka.items():
            for c,q in l[b].items(): acc[c]+=p*q
        out[a]=norm(acc)
    return out

# Binary writer obstruction's forced equations.
r={0:F(1,2),1:F(1,2)}
assert push(r, lambda b:1^b)==r
assert all((1^b)==(b^1) for b in (0,1))
assert all(w!=(1^w) for w in (0,1))
# Joint-law writer repair has a nontrivial terminal fixed point.
h={(0,'*'):F(1,2),(1,'*'):F(1,2)}
assert push(h,lambda x:(x[0]^1,x[1]))==h

# Genuinely dependent probability family: R_s singleton, R_t two points.
f={'*':{0:F(1,2),1:F(1,2)}}
g={0:{'s':F(1)},1:{'s':F(1,2),'t':F(1,2)}}
R={'s':{'a':F(1)}, 't':{'b':F(1,3),'c':F(2,3)}}
joint={}
for b,p in f['*'].items():
    for c,q in g[b].items():
        for resource,v in R[c].items(): joint[b,c,resource]=p*q*v
marginal=push(joint,lambda t:(t[1],t[2]))
direct={(c,r):p*q for c,p in compose(f,g)['*'].items() for r,q in R[c].items()}
assert marginal==direct
assert len(joint)==4 and len(direct)==3
assert sum(joint.values())==sum(direct.values())==1

# Three transports: both comparison paths forget b,c and agree pointwise.
t={'s':{'v':F(1,3),'w':F(2,3)}, 't':{'v':F(3,4),'w':F(1,4)}}
S={'v':{'x':F(1)}, 'w':{'y':F(2,5),'z':F(3,5)}}
full={}
for b,p in f['*'].items():
    for c,q in g[b].items():
        for d,v in t[c].items():
            for s,w in S[d].items(): full[b,c,d,s]=p*q*v*w
left=push(push(full,lambda x:(x[1],x[2],x[3])),lambda x:(x[1],x[2]))
right=push(push(full,lambda x:(x[0],x[2],x[3])),lambda x:(x[1],x[2]))
assert left==right==push(full,lambda x:(x[2],x[3]))
assert compose(compose(f,g),t)==compose(f,compose(g,t))

# Unit-context preservation fails for mixture along a fair bit.
unit_reindexed={(b,'*'):p for b,p in f['*'].items()}
assert len(unit_reindexed)==2
assert len({'*':F(1)})==1

# Persistent once-sampled state policy versus fresh repeat sampling.
q={'b':F(1,3),'c':F(2,3)}
persistent={(x,x):p for x,p in q.items()}
fresh={(x,y):p*v for x,p in q.items() for y,v in q.items()}
assert sum(p for (x,y),p in persistent.items() if x!=y)==0
assert sum(p for (x,y),p in fresh.items() if x!=y)==F(4,9)

# Positive-probability empty resource fibre produces missing mass, not a normalized law.
partial={'ok':{'r':F(1)},'blocked':{}}
k={'*':{'ok':F(3,4),'blocked':F(1,4)}}
assert sum(compose(k,partial)['*'].values())==F(3,4)
# An explicit abort branch conserves mass and its causal information.
with_abort={'ok':{'r':F(1)},'blocked':{('abort','empty_resource'):F(1)}}
assert sum(compose(k,with_abort)['*'].values())==1

# Finite laws quotient experiment presentations: every presentation maps
# measure-preservingly to its support/output representative.
assert push(joint,lambda x:(x[1],x[2]))==direct

# Local reflection: a target support experiment forces the unique output map.
P={0:F(1,2),1:F(1,3),2:F(1,6)}
output={0:'x',1:'x',2:'y'}
K=push(P,output.__getitem__)
valid=[]
for values in product(K, repeat=len(P)):
    phi=dict(zip(P,values))
    if all(phi[x]==output[x] for x in P) and push(P,phi.__getitem__)==K:
        valid.append(phi)
assert len(valid)==1
assert valid[0]==output
# The joint-to-marginal comparator cannot be an isomorphism.
assert len(joint)!=len(direct)

# Full-global-policy recipe: unbalanced history interfaces change cardinalities/laws.
policies_bc=list(product((0,1),repeat=4))
policies_c=list(product((0,1),repeat=2))
assert len(policies_bc)==16 and len(policies_c)==4
laws_bc={F(sum(v),4) for v in policies_bc}
laws_c={F(sum(v),2) for v in policies_c}
assert F(1,4) in laws_bc and F(1,4) not in laws_c
resource_fibres={0:('usable',),1:()}
assert len(resource_fibres[0])==1
assert list(product(resource_fibres[0],resource_fibres[1]))==[]

print('All exact finite checks passed.')
print('Dependent joint:', {str(k):str(v) for k,v in joint.items()})
print('Forgotten-middle law:', {str(k):str(v) for k,v in direct.items()})
print('Persistent unequal-repeat probability: 0')
print('Fresh unequal-repeat probability: 4/9')
print('Missing-resource successful mass: 3/4; explicit abort mass: 1/4')
