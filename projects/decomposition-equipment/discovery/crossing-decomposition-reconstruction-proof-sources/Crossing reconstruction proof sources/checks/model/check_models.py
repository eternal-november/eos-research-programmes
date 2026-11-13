"""Finite checks for explicitly named domains; not a theorem prover."""
from itertools import product, combinations
from collections import defaultdict
import json

def factors(states, obs, out):
    values = {}
    for x in states:
        key, value = obs(x), out(x)
        if key in values and values[key] != value:
            return False
        values[key] = value
    return True

def kernel(states, obs):
    return {(i,j) for i,x in enumerate(states) for j,y in enumerate(states) if obs(x)==obs(y)}

def join(n, *relations):
    parent=list(range(n))
    def root(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]]; i=parent[i]
        return i
    for rel in relations:
        for i,j in rel:
            parent[root(i)]=root(j)
    return {(i,j) for i in range(n) for j in range(n) if root(i)==root(j)}

states=list(product(range(2), repeat=4))
a=lambda x:x[2]^x[3]
b=lambda x:x[1]^x[3]
h=lambda x:x[1]^x[2]^x[3]
p=lambda x:(x[0],x[1],a(x))
q=lambda x:(x[0],x[2],b(x))
t=lambda x:(x[0],a(x),b(x))
assert factors(states,p,h) and factors(states,q,h)
assert not factors(states,t,h)
for j in (1,2,3):
    assert factors(states,lambda x,j=j:(t(x),x[j]),h)
K=join(len(states),kernel(states,p),kernel(states,q))
H=kernel(states,t)
assert K==kernel(states,lambda x:(x[0],h(x)))
assert not H <= K
assert H & K == {(i,i) for i in range(len(states))}

# Every Boolean function on three variables, every raw observation subset.
# Here output is scalar; this directly checks the primitive factorization lemma.
states3=list(product(range(2),repeat=3))
scalar_checks=0
for table in product(range(2),repeat=8):
    out=dict(zip(states3,table)).__getitem__
    essential={j for j in range(3) if any(out(x)!=out(tuple(v^(i==j) for i,v in enumerate(x))) for x in states3)}
    for mask in range(8):
        S={j for j in range(3) if mask>>j&1}
        assert factors(states3,lambda x,S=S:tuple(x[j] for j in sorted(S)),out)==(essential<=S)
        scalar_checks+=1

families=[]
for r in (2,3,4):
    n=2**r; k=n-2
    st=list(product(range(2),repeat=n))
    # Direct truth-table dependence witnesses and whole update, not graph input.
    def f(x):
        zeros=x.count(0)
        return tuple(int(zeros-(x[i]==0)==0) for i in range(n))
    for i in range(n):
        for j in range(n):
            x=(1,)*n; y=tuple(int(t!=j) for t in range(n))
            assert (f(x)[i]!=f(y)[i]) == (i!=j)
    rows=[]
    for mask in range(1<<r):
        cuts=[j for j in range(r) if mask>>j&1]
        blocks=defaultdict(list)
        for i in range(n):
            blocks[tuple((i>>j)&1 for j in cuts)].append(i)
        good=True
        for U in blocks.values():
            B=[j for j in range(n) if j not in U]
            good &= len(B)<=k
            # Exhaust all actual states and verify exact local updates via one
            # extensional conjunction bit, then raw implementation equality.
            for x in st:
                outside=all(x[j] for j in B)
                local=tuple(int(outside and all(x[j] for j in U if j!=i)) for i in U)
                assert local==tuple(f(x)[i] for i in U)
        assert good==(len(cuts)<r)
        rows.append({'cuts':cuts,'block_sizes':list(map(len,blocks.values())), 'admissible':good})
    families.append({'r':r,'n':n,'budget':k,'states':len(st),'subfamilies':rows})

print(json.dumps({'status':'PASS','xor_states':16,'xor_kernel_pairs':{'K':len(K),'H':len(H)},'all_three_input_boolean_scalar_factorizations':scalar_checks,'and_families':families},indent=2))
