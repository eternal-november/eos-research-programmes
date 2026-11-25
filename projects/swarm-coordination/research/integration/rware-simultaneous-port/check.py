"""Selected native simultaneous RWARE steps; independent graph and subset checks."""
import hashlib,itertools,json,sys
from pathlib import Path
if Path(__file__).with_name('isolated.py').exists(): import isolated as iso
else:
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'rware-source-and-return'))
    import replay as iso
import numpy as np
from random import Random

def find_cycle(g):
    for s in g.s:
        track=[]; visit={}
        while s in g.s and s not in visit:
            visit[s]=len(track);track.append(s);s=g.s[s]
        if s in visit:
            return [(v,g.s[v]) for v in track[visit[s]:]]
    raise iso.NoCycle

def longest_path(g):
    # Acyclic weak component with injective nonstationary targets is one chain.
    starts=set(g.s)-set(g.s.values())
    assert len(starts)==1 and len(set(g.s.values()))==len(g.s)
    out=[starts.pop()]
    while out[-1] in g.s:out.append(g.s[out[-1]])
    assert len(out)==len(g.s)+1
    return out

def engine(src):
    iso.nx.algorithms=iso.NS(find_cycle=find_cycle,dag_longest_path=longest_path)
    return iso.load_native(src)

def plant(n,positions,dirs,shelves=(),goal=None,request=()):
    n.Agent.counter=n.Shelf.counter=0
    agents=[n.Agent(*p,d,0) for p,d in zip(positions,dirs)]
    sh=[]
    for key,p in shelves:
        s=n.Shelf(*p);sh.append(s)
        if key is not None: agents[key].carrying_shelf=s
    w=iso.NS(grid_size=(5,5),msg_bits=0,n_agents=len(agents),agents=agents,
             grid=np.zeros((2,5,5),dtype=int),goals=[] if goal is None else [goal],
             highways=np.zeros((5,5),dtype=bool),shelfs=sh,request_queue=[sh[j] for j in request],
             reward_type=n.RewardType.TWO_STAGE,np_random=iso.OneChoice(),_cur_steps=0,
             _cur_inactive_steps=0,max_steps=50,max_inactivity_steps=None,
             _make_obs=lambda a:None,_get_info=lambda:{})
    w._recalc_grid=lambda:n._recalc_grid(w)
    w._is_highway=lambda x,y:n._is_highway(w,x,y)
    if goal:w.highways[goal[1],goal[0]]=True
    w._recalc_grid()
    return w

def intended(pos,req):
    return {i for i,t in enumerate(req) if t!=pos[i]}

def eligible(pos,req,mask,shelves):
    unloaded_shelves={p for i,p in shelves if i is None}
    loaded={i for i,p in shelves if i is not None}
    return {i for i in mask if not (i in loaded and req[i] in unloaded_shelves)}

def reference(pos,req,mask,shelves):
    options=eligible(pos,req,mask,shelves)
    win=set()
    for k in range(len(options)+1):
        for active in itertools.combinations(sorted(options),k):
            out=[req[i] if i in active else p for i,p in enumerate(pos)]
            if len(set(out))!=len(out):continue
            if any(pos[j]==req[i] and pos[i]==req[j] for i,j in itertools.combinations(active,2)):continue
            win.update(active)
    return win

def stencil(pos,req,i):
    m=intended(pos,req)
    p={u:j for j,u in enumerate(pos)}
    dep=[]
    while i in m:
        if i in dep:
            if len(dep)-dep.index(i)==2:return None
            return frozenset(dep)
        dep.append(i)
        if req[i] not in p:return frozenset(dep)
        i=p[req[i]]
    return None

def native(n,pos,req,dirs,mask,shelves=()):
    w=plant(n,pos,dirs,shelves)
    n.step(w,[int(i in mask) for i in range(len(w.agents))])
    out=[(a.x,a.y) for a in w.agents]
    assert len(set(out))==len(out)
    return {i for i,p in enumerate(pos) if p!=out[i]}

def scenarios(n):
    P=((1,1),(2,1),(2,2),(1,2),(3,3)); D=n.Direction
    ds=(D.RIGHT,D.DOWN,D.LEFT,D.UP,D.RIGHT)
    rows=[]
    for masked,stand in itertools.product((False,True),repeat=2):
        w=plant(n,P,ds,((0,P[0]),(3,P[3]),(None if stand else 1,P[1])),P[0],[1])
        w.np_random=iso.NS(choice=lambda C:next(s for s in C if s.id==1))
        w.agents[0].has_delivered=True
        submitted=[1,1,0 if masked else 1,1,1]
        _,pay,*_=n.step(w,submitted)
        moved=[i for i,a in enumerate(w.agents) if (a.x,a.y)!=P[i]]
        assert moved==([4] if (masked or stand) else list(range(5)))
        assert sum(pay)==(0 if (masked or stand) else .5)
        assert w.agents[0].has_delivered and w.agents[0].carrying_shelf is w.shelfs[0]
        assert w.grid[0,P[0][1],P[0][0]]!=0
        assert w.request_queue[0] is w.shelfs[int(masked or stand)]
        recovered=1
        if stand:
            a=[0,n.Action.TOGGLE_LOAD.value,0,0,0]
            assert sum(n.step(w,a)[1])==0 and w.agents[1].carrying_shelf is w.shelfs[2]
            recovered+=1
        if stand or masked:
            assert sum(n.step(w,[1,1,1,1,0])[1])==.5
            assert w.agents[0].has_delivered and w.agents[0].carrying_shelf is w.shelfs[0]
            recovered+=1
        rows.append(dict(delivery_tick=recovered,masked_remote=masked,standing_instead_of_carried=stand,
                         moved=moved,rewards=pay,old_return_owed=True))
    return rows

def main(src):
    n=engine(src); count=0; commits=0; check_dep=0; support_size=0
    C=[(x,y) for y in range(2) for x in range(3)]
    D=n.Direction
    dirs={(0,1):D.DOWN,(0,-1):D.UP,(1,0):D.RIGHT,(-1,0):D.LEFT}
    for k in range(1,len(C)+1):
        for pos in itertools.combinations(C,k):
            choices=[[p,*[q for q in C if abs(q[0]-p[0])+abs(q[1]-p[1])==1]] for p in pos]
            for req in itertools.product(*choices):
                m=intended(pos,req)
                if len({req[i] for i in m})!=len(m):continue
                ds=[dirs.get((q[0]-p[0],q[1]-p[1]),D.UP) for p,q in zip(pos,req)]
                supports={i:stencil(pos,req,i) for i in m}
                for bits in itertools.product((False,True),repeat=len(m)):
                    mask={i for i,b in zip(sorted(m),bits) if b}
                    ref=reference(pos,req,mask,())
                    calc={i for i,s in supports.items() if s is not None and s<=mask}
                    assert ref==calc==native(n,pos,req,ds,mask)
                    count+=1; commits+=len(ref); check_dep+=len(m)
                for i,s in supports.items():
                    if s is None:continue
                    assert i in reference(pos,req,m,())
                    for j in s:assert i not in reference(pos,req,m-{j},())
                    support_size=max(support_size,len(s))
    rng=Random(20913); cargo_checks=0
    for _ in range(5200):
        pos=tuple(rng.sample(C,rng.randrange(1,len(C)+1)))
        req=tuple(rng.choice([p,*[q for q in C if abs(q[0]-p[0])+abs(q[1]-p[1])==1]]) for p in pos)
        m=intended(pos,req)
        if len({req[i] for i in m})!=len(m):continue
        ds=[dirs.get((q[0]-p[0],q[1]-p[1]),D.UP) for p,q in zip(pos,req)]
        loaded={i for i in range(len(pos)) if rng.randrange(2)}
        left=[v for v in C if v not in {pos[i] for i in loaded}]
        shelves=tuple((i,pos[i]) for i in sorted(loaded))+tuple((None,p) for p in left if rng.randrange(2))
        mask={i for i in m if rng.randrange(3)}
        ok=eligible(pos,req,mask,shelves)
        calc={i for i in m if (s:=stencil(pos,req,i)) is not None and s<=ok}
        assert calc==reference(pos,req,mask,shelves)==native(n,pos,req,ds,mask,shelves)
        cargo_checks+=1
    # Explicit native two-way swap, not merely endpoint permutation.
    p=((1,1),(2,1))
    assert native(n,p,p[::-1],[D.RIGHT,D.LEFT],{0,1})==set()
    return dict(cargo_controls=cargo_checks,native_subsets=count,committed_moves=commits,
                dependency_predicates=check_dep,max_least_support=support_size,
                warehouse=scenarios(n),native_two_swap_refused=True)

if __name__=='__main__':
    x=main(Path(sys.argv[1])/'native_source.py')
    v=json.dumps(x,sort_keys=True,separators=(',',':'))+'\n'
    print(v,end=''); print(hashlib.sha256(v.encode()).hexdigest(),file=sys.stderr)
