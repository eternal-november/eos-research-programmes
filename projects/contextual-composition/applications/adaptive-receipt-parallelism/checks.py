"""Finite checks for adaptive snapshot receipt serializability. Standard library only."""
import itertools, json, random
from pathlib import Path

def run(p,s):
    receipt=[]
    def read(k):
        receipt.append((k,s[k])); return s[k]
    # Query selector, then a branch-dependent location; output branch value.
    selector,left,right,target,flip=p
    branch=read(selector)
    value=read(right if branch else left)
    return tuple(receipt), {target:value^flip}, value

def graph(results,s):
    changed={k:i for i,(_,w,_) in enumerate(results) for k,v in w.items() if v!=s[k]}
    return {(i,changed[k]) for i,(r,_,_) in enumerate(results) for k,v in r if k in changed and changed[k]!=i}

def preserves(programs,s,order,results):
    t=dict(s)
    for i in order:
        actual=run(programs[i],t)
        if actual!=results[i]: return False
        t.update(actual[1])
    return True

def linear(order,edges):
    rank={x:i for i,x in enumerate(order)}
    return all(rank[a]<rank[b] for a,b in edges)

def check(programs,s):
    rs=[run(p,s) for p in programs]; es=graph(rs,s)
    for order in itertools.permutations(range(len(programs))):
        assert preserves(programs,s,order,rs)==linear(order,es),(programs,s,order,es)
    return len(list(itertools.permutations(range(len(programs)))))

# Exhaust all two-task adaptive programs on two Boolean cells, fixed unique writers.
count=0; cases=0
variants=list(itertools.product(range(2),range(2),range(2),range(2)))
for bits in itertools.product(range(2),repeat=2):
    s=dict(enumerate(bits))
    for a,b in itertools.product(variants,repeat=2):
        ps=[(*a[:3],0,a[3]),(*b[:3],1,b[3])]
        count+=check(ps,s); cases+=1
rng=random.Random(20261113)
for _ in range(4000):
    s={i:rng.randrange(2) for i in range(5)}
    ps=[(rng.randrange(5),rng.randrange(5),rng.randrange(5),i,rng.randrange(2)) for i in range(4)]
    count+=check(ps,s); cases+=1
# Branch-sensitive edge appears only on selected branch, while writes are disjoint.
s={0:0,1:0,2:0,3:0}
a=(0,1,2,3,0); b=(1,1,1,2,1)
r=[run(p,s) for p in [a,b]]; assert (0,1) not in graph(r,s)
s[0]=1; r=[run(p,s) for p in [a,b]]; assert (0,1) in graph(r,s)
# Classic mutual read/write cycle, including changed-value outputs.
s={0:0,1:0}; ps=[(1,1,1,0,1),(0,0,0,1,1)]
r=[run(p,s) for p in ps]; assert graph(r,s)=={(0,1),(1,0)}
assert not any(preserves(ps,s,p,r) for p in itertools.permutations(range(2)))
# No-op commits induce no graph edge.
ps=[(1,1,1,0,0),(0,0,0,1,0)]; r=[run(p,s) for p in ps]; assert not graph(r,s)
summary={'program_store_cases':cases,'orders_checked':count,'exhaustive_two_cell_cases':1024,'random_seed':20261113,'branch_sensitivity':'passed','cycle':'passed','no_op':'passed','scope':'finite diagnostics, not formal proof'}
Path(__file__).with_name('check-results.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
