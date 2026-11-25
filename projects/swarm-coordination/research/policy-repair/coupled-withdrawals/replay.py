"""Exact withdrawal closure for fixed queues; ordinary Horn is a matched baseline."""
from collections import defaultdict,deque
from itertools import combinations,product
from random import Random
from json import dumps

def okay(queues,D):
    for q in queues:
        head=next((bit for v,bit in q if v not in D),False)
        if head:return False
    return True

def closure(queues,seed):
    D=set(seed)
    pending=deque(range(len(queues)))
    position=[0]*len(queues)
    waiting=defaultdict(list)
    scans=0
    while pending:
        l=pending.popleft(); q=queues[l]
        p=position[l]
        while p<len(q):
            x,blocking=q[p];scans+=1
            if x not in D and not blocking:
                waiting[x].append(l)
                break
            if x not in D:
                D.add(x)
                pending.extend(waiting.pop(x,()))
            p+=1
        position[l]=p
    return D,scans

def brute(queues,seed,universe):
    checks=0; joint=None
    for r in range(len(universe)+1):
        for t in combinations(universe,r):
            D=set(t)
            if not seed<=D:continue
            checks+=1
            if okay(queues,D): joint=D if joint is None else joint&D
    assert joint is not None
    return joint,checks

def horn(queues,seed):
    # Direct linear-size Horn presentation shares prefix nodes within each queue.
    triggers=defaultdict(list); outputs=[]; left=[]
    def add(inputs,output):
        k=len(outputs);outputs.append(output);left.append(len(inputs))
        for i in inputs:triggers[i].append(k)
    for l,q in enumerate(queues):
        add([],('p',l,0))
        for j,(v,b) in enumerate(q):
            here=('p',l,j)
            add([here,('d',v)],('p',l,j+1))
            if b:add([here],('d',v))
    work=deque([('d',v) for v in seed]+[v for k,v in enumerate(outputs) if left[k]==0])
    true=set()
    while work:
        v=work.popleft()
        if v in true:continue
        true.add(v)
        for k in triggers[v]:
            left[k]-=1
            if left[k]==0:work.append(outputs[k])
    return {v[1] for v in true if v[0]=='d'}

def compose(parts,seed,shared):
    # Interface fixed point: all component-local closures use only their
    # original seed and common boundary. Export no internal claim IDs.
    sig=[{v for q in qs for v,_ in q} for qs in parts]
    X=seed&shared
    while True:
        L=[closure(qs,(seed&scope)|(X&scope))[0] for qs,scope in zip(parts,sig)]
        X1=X|((set().union(*L))&shared)
        if X1==X:return seed|set().union(*L)
        X=X1

def run():
    rng=Random(191865); exact=0; comparator_checks=0; authority_checks=0
    contracts=0
    for _ in range(1600):
        V=list(range(rng.randint(1,7)))
        Q=[[ (v,bool(rng.randint(0,1))) for v in rng.sample(V,rng.randrange(len(V)+1))]
            for i in range(rng.randint(1,6))]
        S={v for v in V if rng.randrange(5)==0}
        X,eff=closure(Q,S); Qs=[Q[::2],Q[1::2]]
        B={v for q in Qs[0] for v,_ in q}&{v for q in Qs[1] for v,_ in q}
        ref,n=brute(Q,S,V)
        assert okay(Q,X) and X==ref==horn(Q,S)==compose(Qs,S,B)
        co={v:rng.randrange(5) for v in V};limit=rng.randrange(12)
        W={v for v in V if rng.randrange(4)!=0}
        actual=X<=W and sum(co[v] for v in X)<=limit
        any_ok=False
        for bits in product((False,True),repeat=len(V)):
            D={v for v,b in zip(V,bits) if b}
            corresponding=S<=D<=W and sum(co[v] for v in D)<=limit and okay(Q,D)
            any_ok|=corresponding
            authority_checks+=1
        assert any_ok==actual
        exact+=1;comparator_checks+=n
    n=4096
    Q=[[(i-1,False),(i,True)] for i in range(1,n)]+[[(0,True)]]
    must,scan=closure(Q,set())
    assert len(must)==n and scan==3*n-2
    assert must==horn(Q,set()) and must==compose([Q[::2],Q[1::2]],set(),set(range(n-1)))
    # Same boundary with materially different private cost under one legal seed.
    a=[[(0,False),(1,True)]];b=[[(0,False),(2,False)]]
    for S in (set(),{0}):
        A=closure(a,S)[0];B=closure(b,S)[0]
        assert A&{0}==B&{0}
    assert closure(a,{0})[0]-{0}=={1} and closure(b,{0})[0]-{0}==set()
    return dict(families=exact,legal_sets_considered=comparator_checks,
                authorization_and_budget_checks=authority_checks,chain_claims=n,
                chain_work=scan,private_cost_counterexample=True)
if __name__=='__main__': print(dumps(run(),sort_keys=True,separators=(',',':')))
