"""Operational descent of separate context/content projections.

Fixed nominal effect clock serial only for the finite congruence.
The separate SQLite trace suite preserves actual committed serials.
"""
from kernel import State,step,section
from collections import deque,defaultdict
from itertools import product
import json
OPS=(('attest',1),('attest',2),('handoff',0),('handoff',11),
     ('apply',10),('apply',11),('inspect',10),('inspect',11))

def advance(s,a):
    if a[0]=='handoff' and s.law.holder!=10:return s,('unavailable',)
    return step(s,a,1)

def live_set():
    q=deque([State()]);s={q[0]}
    while q:
        x=q.popleft()
        for a in OPS:
            y,_=advance(x,a)
            if y not in s:s.add(y);q.append(y)
    return sorted(s,key=repr)

def quotient(states,audit):
    def base_key(s):return section(s,audit)
    unique={x:i for i,x in enumerate(sorted(set(map(base_key,states)),key=repr))}
    p={s:unique[base_key(s)] for s in states}
    oldn=0
    while oldn!=len(set(p.values())):
        oldn=len(set(p.values()))
        blocks={}
        for s in states:
            branches=tuple((label,p[x]) for x,label in (advance(s,a) for a in OPS))
            k=(p[s],branches)
            blocks.setdefault(k,len(blocks))
        p={s:blocks[(p[s],tuple((label,p[x]) for x,label in (advance(s,a) for a in OPS)))] for s in states}
    return p

def projection(s,kind):
    facts=(s.facts.receipt,s.facts.clear())
    if kind=='history-only':return facts
    if kind=='audit':facts=(s.facts.receipt,s.facts.witnesses)
    return (s.law.holder,*facts)

def profile_descent(states,kind,audit=False,transition=True):
    # This is a direct source -> target test for the displayed projection,
    # not an unverified claim about operationally unrelated histories.
    fibers=defaultdict(set)
    for s in states:
        key=projection(s,kind)
        obs=section(s,audit)
        successor=tuple((o,projection(xs,kind)) for xs,o in (advance(s,a) for a in OPS))
        fibers[key].add((obs,successor) if transition else obs)
    return len(fibers),sum(len(x)>1 for x in fibers.values())

s=live_set()
p=quotient(s,False);q=quotient(s,True)
assert profile_descent(s,'body-law')[-1]==0
assert profile_descent(s,'audit',True)[-1]==0
assert profile_descent(s,'body-law',True)[-1]>0
assert profile_descent(s,'history-only',transition=False)[-1]>0
witnesses={}
for a,b in product(s,repeat=2):
    if a.law.holder==10 and b.law.holder==11 and a.facts==b.facts and a.facts.receipt is None and a.facts.clear():
        assert projection(a,'history-only')==projection(b,'history-only')
        assert not section(a)==section(b)
        witnesses['owner']=True
    if a.law==b.law and a.facts.receipt==b.facts.receipt and {a.facts.witnesses,b.facts.witnesses}=={1,2}:
        assert projection(a,'body-law')==projection(b,'body-law')
        assert p[a]==p[b] and q[a]!=q[b]
        witnesses['provenance']=True
assert len(witnesses)==2
print(json.dumps(dict(states=len(s),effect_classes=len(set(p.values())),
                      audit_classes=len(set(q.values())),
                      extent={k:profile_descent(s,k,k=='audit') for k in
                                  ('history-only','body-law','audit')},
                      witnesses=witnesses),sort_keys=True))
