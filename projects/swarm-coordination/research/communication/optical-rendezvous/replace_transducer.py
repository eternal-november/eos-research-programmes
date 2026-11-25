import contextlib,hashlib,io,json
from itertools import product
with contextlib.redirect_stdout(io.StringIO()):
    import replay as r
SET=-6
DIGEST="208fc5f93de281dea7568f48cada4fefd9e1fcd8d26b679500ca3251399cbfaa"
bp=open("receiver_policy.json","rb").read()
assert hashlib.sha256(bp).hexdigest()==DIGEST

def tuples(x):
    return tuple(tuples(z) for z in x) if isinstance(x,list) else x

policy={tuples(k):a for k,a in json.loads(bp)}
assert len(policy)==11

def run(w,busy,latency,issue,damaged=False,witness=False):
    # Retain source report until an actual co-located transfer.
    # A recognizes its local blocked edge. Modelled physical mechanical
    # flag hardens only after SET and the given positive latency.
    s=r.INIT; hist=(); marked=None; trace=[]
    for t in range(7):
        key=hist+(r.view(w,s,1),)
        if key not in policy:return None
        b=policy[key];hist=key+((b,),)
        assert b in r.possible(w,s,1,True)
        if t==issue:
            if t<busy or s[0]!=r.REFUGE:return None
            a=SET
        elif t==3:
            choices=r.available(w,s[0])
            assert s[0]==r.REFUGE and len(choices)==1
            a=choices[0]
        elif t==4:a=r.GIVE
        elif t==6:a=r.REFUGE
        else:a=r.WAIT
        if a!=SET and a not in r.possible(w,s,0,True):return None
        new=r.step(w,s,a,b,t)
        if new is None:return None
        if b==r.LISTEN and not damaged and marked is not None and marked+latency<=t:
            new=new[:-1]+(w[0],)
        if a==SET:marked=t
        trace.append((t,a,b,new))
        s=new
        assert s[4]
    if not (s[0]==r.REFUGE and s[1]==r.BASE and s[3]==2):return None
    return trace if witness else True

checks=0
for busy,latency,damaged in product(range(7),range(1,7),(False,True)):
    easy,hard=r.nom
    a=(None,)+tuple(range(busy,3))
    good=all(any(run(w,busy,latency,t,damaged) for t in a) for w in (easy,hard))
    assert good==(not damaged and busy+latency<=2),(busy,latency,damaged,good)
    checks+=1
print("frozen receiver",DIGEST)
print(checks,"scope-preservation comparisons")
print("setup before required cut works",run(r.nom[1],0,2,0,witness=True))
print("same latency, one tick of prior work misses",run(r.nom[1],1,2,1))
