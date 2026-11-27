"""Held-in known-map game; actual report bytes from native broker, no oracle in its local cut."""
from collections import deque
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from pathlib import Path
import json, math, sqlite3, subprocess, tempfile
from replay import inputs
ROOT=Path(__file__).parent
DOCK,EXIT,SCOUT,START=39,0,3,43
GATE=(2,3)
KEY="IR:3/run7"

def load_native(g,coords,distances):
    sites=(3,2,39)
    ends=[coords[3],coords[39],(49,50,0),(51,50,0)]
    assert ends[:2]==[(75,50,0),(50,25,0)]
    cases=[];raw=["3"]
    for cap in (24.9,25.51,26.1):
        raw.append(" ".join(map(str,(*sites,*(distances[i][j] for i in sites for j in sites),
                                    *(x for v in ends for x in v),cap))))
    native=subprocess.run([str(ROOT/"terminal")],input="\n".join(raw)+"\n",text=True,
                             capture_output=True,check=True).stdout
    for i,record in enumerate(native.splitlines()):
        _,_,_,mode,updates,ct,vis,relays,front,power,route,seen,rx,side,tx,payload=record.split()
        assert int(tx)==len(KEY) and side=="1"
        assert (seen,rx)==(("1",str(len(KEY))) if payload==KEY else ("0","0"))
        assert payload in (KEY,"-")
        if mode in ("ab","ba"):
            cases.append((i//8,mode,payload))
    assert cases==[(0,"ab","-"),(0,"ba","-"),(1,"ab","-"),(1,"ba",KEY),
                   (2,"ab",KEY),(2,"ba",KEY)]
    return cases

@dataclass(frozen=True)
class W:
    initial: bool
    closed: bool
    unavailable_through: int

@dataclass(frozen=True)
class State:
    pos:int=START
    t:int=0
    carry:bool=False
    deposited:bool=False
    inspected:bool=False

def known(s,w,gate_tick):
    if s.t>=gate_tick and s.pos in GATE:return "closed" if w.closed else "open"
    return "interlock-out-of-sight"

def transition(graph,s,act,w,gate_tick,inspect,report_due,inspect_due):
    p,t,carry,deposited,inspected=s.pos,s.t+1,s.carry,s.deposited,s.inspected
    if act[0]=="move":
        edge=tuple(sorted((p,act[1])))
        assert act[1] in graph[p]
        assert not (edge==GATE and s.t>=gate_tick and w.closed)
        p=act[1]
    elif act==("collect",):
        assert p==SCOUT
        carry=True
    elif act==("deposit",):
        assert p==DOCK and carry
        if t<=report_due:deposited=True
        carry=False
    elif act==("inspect",):
        assert p==inspect
        if t<=inspect_due:inspected=True
    else:assert act in (("read",),("wait",))
    return State(p,t,carry,deposited,inspected)

def signature(act,n,w,mode,earned):
    if act!=("read",):return None
    if mode=="none" or n.t<=w.unavailable_through:return "unavailable"
    if mode=="positive" and not (n.deposited or w.initial):return "unavailable"
    return earned or ("present" if n.deposited or w.initial else "verified-absent")

def actions(graph,s,local,mode,inspect,report_due,inspect_due):
    v=[("move",x) for x in sorted(graph[s.pos])
       if not (local=="closed" and tuple(sorted((s.pos,x)))==GATE)]
    if s.pos==DOCK and mode!="none":v.append(("read",))
    if s.pos==SCOUT and not (s.carry or s.deposited) and s.t<report_due:v.append(("collect",))
    if s.pos==DOCK and s.carry and not s.deposited and s.t<report_due:v.append(("deposit",))
    if s.pos==inspect and not s.inspected and s.t<inspect_due:v.append(("inspect",))
    return [*v,("wait",)]

def synth(graph,worlds,mode,gate_tick,inspect,report_due,inspect_due,egress,require_inspect,fast_egress=None):
    # Every call is indexed by possible worlds compatible with the accumulated
    # local history. Gate is observed only at an endpoint inside its local seam.
    # All these worlds share the same measured mover state.
    menu={}
    @lru_cache(None)
    def solve(s,world_ids):
        local=known(s,worlds[world_ids[0]],gate_tick)
        assert all(local==known(s,worlds[i],gate_tick) for i in world_ids)
        local_due=min(egress,fast_egress) if fast_egress is not None and any(worlds[i].initial for i in world_ids) else egress
        if s.pos==EXIT and s.t<=local_due and (s.deposited or all(worlds[i].initial for i in world_ids)) and (
                s.inspected or not require_inspect):
            return True
        if s.t>=local_due or (require_inspect and s.t>=inspect_due and not s.inspected):return False
        if s.t>=report_due and not s.deposited and not all(worlds[i].initial for i in world_ids):return False
        for act in actions(graph,s,local,mode,inspect,report_due,inspect_due):
            cells={}
            for i in world_ids:
                w=worlds[i]
                ss=transition(graph,s,act,w,gate_tick,inspect,report_due,inspect_due)
                view=(signature(act,ss,w,mode,None),known(ss,w,gate_tick))
                cells.setdefault((ss,view),[]).append(i)
            if all(solve(state,tuple(ids)) for (state,_),ids in cells.items()):
                menu[(s,world_ids)]=(act,{v:(ns,tuple(ids)) for (ns,v),ids in cells.items()})
                return True
        return False
    result=solve(State(),tuple(range(len(worlds))))
    return result,menu,solve.cache_info().currsize

def replay_policy(graph,worlds,mode,gate_tick,inspect,report_due,inspect_due,egress,required,menu,fast_egress=None):
    logs=[]
    for w in worlds:
        with tempfile.TemporaryDirectory() as d:
            db=Path(d)/"terminal.sqlite"
            with sqlite3.connect(db) as h:
                h.execute("CREATE TABLE completed (k TEXT PRIMARY KEY)")
                h.execute("INSERT INTO completed VALUES ('IR:3/prior')")
                if w.initial:h.execute("INSERT INTO completed VALUES (?)",(KEY,))
            s=State(); ids=tuple(range(len(worlds))); log=[]
            while (s,ids) in menu:
                a,cells=menu[(s,ids)]
                q=transition(graph,s,a,w,gate_tick,inspect,report_due,inspect_due)
                actual=None
                if a==("deposit",):
                    # Same named sealed report transferred from scout tile,
                    # deterministic exact copy. Retry is idempotent at dock.
                    with sqlite3.connect(db) as h:h.execute("INSERT OR IGNORE INTO completed VALUES (?)",(KEY,))
                if a==("read",):
                    assert s.pos==DOCK and q.t==s.t+1
                    with sqlite3.connect(db) as h:
                        hit=h.execute("SELECT k FROM completed WHERE k=?",(KEY,)).fetchone()
                    actual="present" if hit else ("unavailable" if mode=="positive" else "verified-absent")
                k=(signature(a,q,w,mode,actual),known(q,w,gate_tick))
                qs,ids=cells[k];assert qs==q
                log.append([s.t,s.pos," ".join(map(str,a)),k])
                s=q
            with sqlite3.connect(db) as h:
                assert h.execute("SELECT k FROM completed WHERE k=?",(KEY,)).fetchone()==(KEY,)
            assert s.pos==EXIT and s.t<=egress and (s.inspected or not required)
            if w.initial and fast_egress is not None: assert s.t<=fast_egress
            assert s.deposited or w.initial
            logs.append(log)
    return logs

def global_bfs(graph,w,gate_tick,inspect,report_due,inspect_due,egress,req):
    # Independent known-plant shortest path on duty-state graph. Its answer
    # must upper-bound every locally implementable solution under same resources.
    q=deque([State()]);seen={State()}
    while q:
        s=q.popleft()
        if s.pos==EXIT and (w.initial or s.deposited) and (s.inspected or not req):return True
        if s.t>=egress:continue
        for a in actions(graph,s,known(s,w,gate_tick),"none",inspect,report_due,inspect_due):
            ns=transition(graph,s,a,w,gate_tick,inspect,report_due,inspect_due)
            if ns not in seen:seen.add(ns);q.append(ns)
    return False

def main():
    graph,coords,dists=inputs()
    prefix=load_native(graph,coords,dists)
    # Verify the geometric inputs of the paper lower bound independently.
    # A separate unweighted BFS derives movement costs for this projection.
    def move_dist(start,end,closed=False):
        q=deque([(start,0)]); seen={start}
        while q:
            a,n=q.popleft()
            if a==end:return n
            for b in graph[a]:
                if b in seen or (closed and tuple(sorted((a,b)))==GATE):continue
                seen.add(b);q.append((b,n+1))
        raise AssertionError("unreachable")
    assert (move_dist(3,39,True),move_dist(39,0),move_dist(43,39),
            move_dist(43,1),move_dist(39,1),move_dist(43,3,True))==(8,3,1,1,2,7)
    # Keep the full graph for contingency synthesis and physical replay.
    main_worlds=tuple(
        W(payload==KEY,closed,False) for band,_,payload in prefix if band==1 for closed in (False,True))
    classes={"split":main_worlds,
             "mixed":main_worlds+tuple(W(w.initial,w.closed,99) for w in main_worlds),
             "first-read-erased":tuple(W(w.initial,w.closed,2) for w in main_worlds),
             "intact":tuple(w for w in main_worlds if not w.closed),
             "nominal":(W(True,False,False),),"contact-only":(W(False,False,False),),
             "gate-only":(W(True,True,False),),"joint":(W(False,True,False),)}
    # Reuse demonstration should not pretend the report and inspection
    # have the same service deadline. Explore separate due cuts.
    outcomes={};witness={};checks=0;cost=0;replayed=0
    for cname,inspect,due,mode in product(classes,(1,8),(8,12,16),("sealed","positive","none")):
        worlds=classes[cname]; gate_tick=3
        rs=[]
        for i,t in enumerate(range(due+2,due+7)):
            args=(gate_tick,inspect,due,due+1,t)
            ans,m,k=synth(graph,worlds,mode,*args,True)
            direct=all(global_bfs(graph,w,*args,True) for w in worlds)
            assert not ans or direct
            if len(worlds)==1:assert ans==direct
            cost+=k; checks+=1
            rs.append((ans,direct))
            if ans:
                logs=replay_policy(graph,worlds,mode,*args,True,m);replayed+=len(logs)
                if i==0 or not any(x[0] for x in rs[:-1]):
                    witness[(cname,inspect,due,mode)]=[t,logs]
        outcomes[(cname,inspect,due,mode)]=rs
    differentiating=[]
    for (cl,ins,d,_) in list(outcomes):
        if _!="sealed":continue
        a=outcomes[(cl,ins,d,"sealed")]; b=outcomes[(cl,ins,d,"none")]
        diff=[i+d+2 for i,((x,_),(y,_)) in enumerate(zip(a,b)) if x and not y]
        if diff:differentiating.append((cl,ins,d,diff))
    # Pareto deadline: never relax the no-receipt branch or the old report.
    # Earlier egress is pledged only on a closed-ledger prior-success history,
    # a performance contract, not a revealed world tag.
    frontier={}
    for cname,report,d,mode in product(("split","mixed","first-read-erased","intact"),(19,20,21,22,23),(23,24,25,26),("sealed","none")):
        ws=classes[cname]
        h=(3,1,report,12,d)
        cutoff=None
        for fast in range(7,d+1):
            res,menu,k=synth(graph,ws,mode,*h,True,fast)
            if res:
                replay_policy(graph,ws,mode,*h,True,menu,fast_egress=fast)
                cutoff=fast
                if (cname,report,d,mode)==("split",21,24,"sealed"):
                    frontier["witness"]=replay_policy(graph,ws,mode,*h,True,menu,fast_egress=fast)
                break
        frontier[f"{cname}/{report}/{d}/{mode}"]=cutoff
        if cname=="split":
            analytic=17
            if mode=="sealed" and report>=21 and d>=24:analytic=10
            if mode=="sealed" and report>=23 and d>=26:analytic=8
            assert cutoff==analytic,(report,d,mode,cutoff,analytic)
    assert frontier["split/20/24/sealed"]==17
    assert frontier["split/21/24/sealed"]==10
    assert frontier["split/21/23/sealed"]==17
    assert frontier["split/22/26/sealed"]==10
    assert frontier["split/23/26/sealed"]==8
    assert frontier["first-read-erased/22/25/sealed"]==11
    assert frontier["mixed/23/26/sealed"]==17
    assert frontier["intact/19/24/sealed"]==8
    assert frontier["split/23/26/none"]==17
    print(json.dumps({"native_prefix":prefix,"decisions":checks,"states":cost,
          "audited_histories":replayed,"separations":differentiating,
          "sample":next((witness[(c,i,d,"sealed")] for c,i,d,_ in differentiating),None),
          "frontier":frontier,"outcomes":{"/".join(map(str,k)):v for k,v in outcomes.items()}},sort_keys=True))
if __name__=="__main__":main()
