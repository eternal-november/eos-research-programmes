from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from brake import step
from functools import lru_cache
from itertools import combinations

def spend(v,word,e,U):
    n=2*v
    if 0<=e<n and e not in U:
        # A timely receipt repeats the named grant immediately.
        return word[:e+1]+(word[e],)+word[e+1:]
    final=word[min(U)] if U else 0
    return word+(final,)

def exec_word(v,acts,e):
    s=(v,v,0);path=[0]
    for t,a in enumerate(acts):
        s=step(s,a,t==e,True)
        path.append(s[2])
    assert s[:2]==(0,0)
    return tuple(path)

def test(v,word,U,cap,sharp=False):
    n=2*v
    states={};actions={}
    for e in range(-1,n+1):
        seq=spend(v,word,e,U)
        for t,a in enumerate(seq):
            view=e if e>=0 and e<t and e not in U else -1
            assert actions.setdefault((t,view),a)==a
        states[e]=exec_word(v,seq,e)
    peak=max(max(map(abs,p)) for p in states.values())
    assert peak<=cap and (not sharp or peak==cap)
    a,b=states[-1],states[min(U)]
    for j in U:
        assert all(min(x,y)<=z<=max(x,y) for x,y,z in zip(a,b,states[j]))
    return len(states)

def existential(v,U,cap):
    H=2*v+1
    @lru_cache(None)
    def can(t,X):
        if any(abs(r)>cap for _,(_,_,r) in X):return False
        if all(a==b==0 for _,(a,b,r) in X):return True
        if any(a+b>H-t-(e>=t) for e,(a,b,r) in X):return False
        for ctrl in (-1,0,1):
            d={}
            for e,s in X:
                new=step(s,ctrl,t==e,True)
                key=e if e>=0 and e<=t and e not in U else -1
                d.setdefault(key,[]).append((e,new))
            if all(can(t+1,tuple(Y)) for Y in d.values()):
                return True
        return False
    return can(0,tuple((e,(v,v,0)) for e in range(-1,H)))

if __name__=='__main__':
    runs=0
    for v in range(2,75):
        nominal=(1,-1,-1,1)*(v//2)+(1,-1)*(v%2)
        spread={i for i,a in enumerate(nominal) if a==1}
        block={0,*range(v+1,2*v)}
        assert len(spread)==len(block)==v and min(spread)==min(block)==0
        runs+=test(v,nominal,spread,4*v)
        burst=(-1,)+(1,)*v+(-1,)*(v-1)
        runs+=test(v,burst,block,2*v*v,True)
        if v<=5:
            assert not existential(v,block,2*v*v-1)
            assert existential(v,block,2*v*v) and existential(v,spread,4*v)
    # Count-bound proof: finite exact direct checks over all receipt
    # relocation masks up to eight nominal slots.
    n=0
    for v in range(1,5):
        for mask in range(1<<(2*v)):
            U=frozenset(i for i in range(2*v) if mask>>i&1)
            assert existential(v,U,2*v*(2*v+1))==(len(U)<=v)
            n+=1
    print(runs,'explicit traces, pointwise hull uses earliest opaque index')
    print(n,'exact two-actor deadline feasibility comparisons over receipt placements')
