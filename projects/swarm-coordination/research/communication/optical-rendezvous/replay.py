"""Finite local-policy synthesis over source histories, not a field model."""
from collections import deque
from functools import cache
from itertools import product

BASE, HUB, LEFT, RIGHT, REFUGE = range(5)
G={(0,1),(1,2),(1,3),(2,4),(3,4)}
WAIT,GIVE,TAKE,BEACON,LISTEN=-1,-2,-3,-4,-5
# Source world: which mobility edge is blocked, and is optical read erased?
def available(w,v):
    closed=(w[0],REFUGE)
    return tuple(sorted(b if a==v else a for a,b in G-{closed} if v in (a,b)))

# x,y, A remaining travel, A custody of old report (0=A,1=B,2=base),
# B's own report delivered, B's latest received optical value (0=absent).
INIT=(REFUGE,HUB,2,0,False,0)

@cache
def distance(w,src,goal):
    d={src:0};q=deque([src])
    while q:
        x=q.popleft()
        if x==goal:return d[x]
        for y in available(w,x):
            if y not in d:d[y]=d[x]+1;q.append(y)
    return 1000

def view(w,s,i):
    x,y,rem,h,b,signal=s
    p=(x,y)[i]
    if i==0:return (p,rem,h==0,x==y,available(w,p))
    return (p,h==1,b,signal,x==y,available(w,p))

def possible(w,s,i,light):
    x,y,rem,h,b,signal=s
    p=(x,y)[i]
    opts=[WAIT]
    if i==1 or rem:opts.extend(available(w,p))
    if x==y and (i==1 or h==0):opts.append(GIVE if i==0 else TAKE)
    if light and ((i==0 and x==REFUGE) or (i==1 and y==HUB)):
        opts.append(BEACON if i==0 else LISTEN)
    return tuple(opts)

def step(w,s,a,b,t):
    x,y,rem,h,own,signal=s
    u=x if a<0 else a;v=y if b<0 else b
    if x!=y and u==y and v==x:return None
    if h==0 and x==y and a==GIVE and b==TAKE:h=1
    if h==0 and u==BASE or h==1 and v==BASE:h=2
    if a==BEACON and b==LISTEN and not w[1]:signal=w[0]
    return (u,v,rem-int(u!=x),h,own or v==BASE,signal)

def split_classes(old,observations):
    keys={}
    return tuple(keys.setdefault((o,z),len(keys)) for o,z in zip(old,observations))

def solve(worlds,H,light,own_due=1,witness=False):
    recipe={}
    @cache
    def reach(t,states,ca,cb):
        for w,s in zip(worlds,states):
            x,y,rem,h,own,signal=s
            if not own and t+distance(w,y,BASE)>own_due:return False
            if t+distance(w,y,BASE)>H:return False
            if min(distance(w,x,REFUGE),distance(w,x,BASE))>min(rem,H-t):return False
            if h<2 and t+distance(w,(x,y)[h],BASE)>H:return False
        if t==H:
            return all(s[0] in (REFUGE,BASE) and s[1]==BASE and s[3]==2 for s in states)
        cla=split_classes(ca,[view(w,s,0) for w,s in zip(worlds,states)])
        clb=split_classes(cb,[view(w,s,1) for w,s in zip(worlds,states)])
        def opts(classes,i):
            labels=range(max(classes)+1)
            return [tuple(sorted(set.intersection(*(set(possible(w,s,i,light))
                    for w,s,k in zip(worlds,states,classes) if k==x)),
                    key=lambda a: (a != WAIT, a in (BEACON, LISTEN), a))) for x in labels]
        for aa in product(*opts(cla,0)):
            for bb in product(*opts(clb,1)):
                out=tuple(step(w,s,aa[i],bb[j],t) for w,s,i,j in zip(worlds,states,cla,clb))
                if None not in out and reach(t+1,out,cla,clb):
                    recipe[t,states,ca,cb]=(aa,bb,out,cla,clb)
                    return True
        return False
    states=(INIT,)*len(worlds);eq=(0,)*len(worlds)
    ok=reach(0,states,eq,eq)
    if witness and ok:
        rows=[]
        ca=cb=eq
        for t in range(H):
            aa,bb,out,na,nb=recipe[t,states,ca,cb]
            rows.append((t,tuple((aa[na[i]],bb[nb[i]],x) for i,x in enumerate(out))))
            states,ca,cb=out,na,nb
        return tuple(rows)
    return ok

nom=((LEFT,False),(RIGHT,False))
erase=((LEFT,True),(RIGHT,True))
for desc,ws,light,expect in [
    ("per-world left",nom[:1],False,6),
    ("per-world right",nom[1:],False,6),
    ("no optical read",nom,False,8),
    ("source-coupled optical read",nom,True,7),
    ("all erased (lower bound for unreliable read)",erase,True,8)]:
    d=next(t for t in range(5,10) if solve(ws,t,light))
    assert d==expect,(desc,d,expect)
    print(desc,"minimum mission deadline",d,flush=True)

print("seven-tick shared policy",solve(nom,7,True,witness=True))

# Execute a full policy as functions of observed histories only. No
# world identity, other-side history or optimizer partition is an input.
def replay_local(worlds,H,light):
    rows=solve(worlds,H,light,witness=True)
    assert rows
    knobs=[{},{}]
    states=[INIT]*len(worlds)
    hist=[[() for _ in worlds] for _ in knobs]
    for _,row in rows:
        for i,(w,s,(a,b,nexts)) in enumerate(zip(worlds,states,row)):
            for actor,act in enumerate((a,b)):
                key=hist[actor][i]+(view(w,s,actor),)
                assert knobs[actor].setdefault(key,act)==act
                hist[actor][i]=key+((act,),)
            states[i]=nexts
    for w in worlds:
        history=[(),()]; state=INIT
        for t in range(H):
            choices=[]
            for actor in range(2):
                key=history[actor]+(view(w,state,actor),)
                v=knobs[actor][key]
                assert v in possible(w,state,actor,light)
                choices.append(v)
                history[actor]=key+((v,),)
            state=step(w,state,*choices,t)
            assert state is not None and state[4]
        assert state[0] in (REFUGE,BASE) and state[1]==BASE and state[3]==2
    return tuple(len(k) for k in knobs)

print("local history tables, reliable optics",replay_local(nom,7,True))
print("local history tables, robust to optional erasure by ignoring optics",replay_local(nom+erase,8,False))

# Independently proved thresholds in the written argument.
checks=0
for ws,light,critical in [(nom[:1],False,6),(nom[1:],False,6),
                          (nom,False,8),(nom,True,7),(erase,True,8)]:
    for deadline in range(4,10):
        assert solve(ws,deadline,light)==(deadline>=critical)
        checks+=1
print("proof threshold comparisons",checks)
