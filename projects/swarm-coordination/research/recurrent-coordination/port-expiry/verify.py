"""Checker does not import model.py or the generation algorithm."""
import json
from fractions import Fraction as F

def normalized(state):
    return tuple((sig,tuple(a)) for sig,a in state)

def from_absolute(T,ages):
    return tuple(sorted(T-o for o in ages))

def verify(data):
    params=data['parameters']
    assert params==[[1,3,4,1],[1,1,6,1]]
    assert data['weights']==[3,2] and data['cap']==2
    vals={normalized(s):p for s,p in data['potential']}
    assert len(vals)==len(data['potential'])
    assert all(isinstance(p,int) for p in vals.values())
    initial=tuple((0,(w,w)) for _,_,w,M in params)
    seen={initial};recent=[initial]
    edges=0
    for s in recent:
        for a in 'AB.':
            n=[]
            for j,(sign,elapsed) in enumerate(s):
                w=params[j][2]
                used=chr(65+j)==a
                # Old records are named by chronological rank, not by the
                # tag checker's deque representation. With M=1 the
                # previous use of this signer is the second most recent.
                prev,last=-elapsed[1],-elapsed[0]
                lastmint_same=prev
                if used and (-last<params[j][sign] or -lastmint_same<w):break
                kept=(last,0) if used else (prev,last)
                n.append(((sign+int(used))%2,
                          tuple(min(age,w) for age in from_absolute(1,kept))))
            else:
                t=tuple(n)
                assert vals[t]-vals[s]>={'A':1,'B':0,'.':-2}[a]
                edges+=1
                if t not in seen:seen.add(t);recent.append(t)
    assert set(vals)==seen
    print(len(seen),edges,'independent potential checks for 3*A+2*B<=2')
    R=set()
    for word in data['witness']:
        assert len(word)>=max(p[2] for p in params)
        assert all(word.count(a)%2==0 for a in 'AB')
        same={};last={};sign={'A':0,'B':0}
        for t,a in enumerate(word*8):
            if a=='.':continue
            j=ord(a)-65
            key=(a,sign[a])
            assert t-last.get(a,-1000)>=params[j][sign[a]]
            assert t-same.get(key,-1000)>=params[j][2]
            same[key]=last[a]=t;sign[a]^=1
        R.add((F(word.count('A'),len(word)),F(word.count('B'),len(word))))
    assert R=={(F(1,2),F(1,4)),(F(4,9),F(1,3))}
    print('both boundary schedules independently replayed with uncapped absolute times')
if __name__=='__main__':
    with open('potential.json') as f:verify(json.load(f))
