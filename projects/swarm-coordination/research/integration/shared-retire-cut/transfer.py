"""Replay a shared admission law with actual local effects and matched policies."""
from itertools import product
import hashlib,json,subprocess,sys
from pathlib import Path

UP=Path(sys.argv[1]).resolve()
sys.path.insert(0,str(UP))
import rware_rotation as rw

ACTIONS="-LR"
MODES=("sampled","skipped","racing","retired","late_retire")

class Warehouse:
    def __init__(self, branch):
        self.branch=branch
        self.pos=((1,0),(3,0),(2,1),(4,3))
        n=rw.engine(UP/"native_source.py")
        d=n.Direction
        self.n=n
        self.w=rw.plant(n,self.pos,(d.DOWN,d.DOWN,d.LEFT if branch=="L" else d.RIGHT,d.UP),
             (*[(i,p) for i,p in enumerate(self.pos)],(None,(0,4)),(None,(1,4)),(None,(2,4))),
             request=(0,1,3))
        self.w.np_random=rw.iso.NS(choice=lambda c:min((s for s in c if s.id>=5),key=lambda s:s.id))
        self.w.agents[2].has_delivered=True
        self.docks=((1,1),(3,1))
        self.original=self.w.shelfs[2]
        self.old_effects=0
    def old_attempt(self, at):
        self.w.goals=[]
        assert sum(self.n.step(self.w,[0,0,1,0])[1])==0
        assert self.old_position()==self.docks[self.branch=="R"]
        assert self.owed()
        self.old_effects+=1
    def idle_old_slot(self):
        assert sum(self.n.step(self.w,[0,0,0,0])[1])==0
    def old_position(self):
        a=self.w.agents[2]
        return a.x,a.y
    def owed(self):
        a=self.w.agents[2]
        return int(a.has_delivered and a.carrying_shelf is self.original)
    def local_sample(self, at):
        # Native grid occupancy of each dock, not a delivery or request flag.
        w=self.w
        return tuple(int(w.grid[0,y,x]!=0) for x,y in self.docks)
    def commit(self, a, at):
        w=self.w
        separate=(4,2)
        w.goals=[*self.docks,separate]
        for x,y in w.goals:w.highways[y,x]=True
        _,pay,*_=self.n.step(w,[int(a=="L"),int(a=="R"),0,1])
        assert sum(pay[:3]) in (0,.5) and pay[2]==0 and pay[3]==.5
        assert (w.agents[3].x,w.agents[3].y)==separate
        assert all(w.agents[i].carrying_shelf is w.shelfs[i] for i in range(4))
        assert len({(g.x,g.y) for g in w.agents})==4
        service=int(sum(pay[:3])==.5)
        if service:
            c=a=="R"
            assert (w.agents[c].x,w.agents[c].y)==self.docks[c]
            assert w.agents[c].has_delivered
        assert self.owed()
        return service,1,self.owed()
    def close(self): pass

class Network:
    def __init__(self, branch):
        self.branch=branch
        self.old_effects=0
        self.p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                                encoding="ascii")
    def call(self,op,a,t):
        self.p.stdin.write(f"{op} {a} {t}\n")
        self.p.stdin.flush()
        row=self.p.stdout.readline().split()
        assert len(row)==5,row
        return tuple(map(int,row[0])),tuple(map(int,row[1:]))
    def old_attempt(self,at):
        busy,(rescue,n,old,owed)=self.call("O",self.branch,at)
        assert busy==(int(self.branch=="L"),int(self.branch=="R"))
        assert (rescue,n,old,owed)==(0,0,0,1)
        self.old_effects+=1
    def local_sample(self,at):
        b,(rescue,n,old,owed)=self.call("P","-",at)
        assert (rescue,n,old,owed)==(0,0,0,1)
        return b
    def commit(self,a,at):
        b,(r,u,old,owed)=self.call("C",a,at)
        assert r in (0,1) and u==1 and old==0
        assert owed
        return r,u,owed
    def idle_old_slot(self): pass
    def close(self):
        self.p.stdin.close()
        self.p.stdout.close()
        assert self.p.wait()==0

class Queue:
    """Only a not-yet-admitted action can be retired at this gate."""
    state="queued"
    def retire(self):
        if self.state=="queued":
            self.state="retired"
            return True
        return False
    def admit(self,run):
        if self.state!="queued": return False
        self.state="admitted"
        run()
        self.state="completed"
        return True

def choose(sample, enclosed):
    # At most one rescue authorization exists; unrelated work uses another.
    if sample is None or not enclosed:return "-"
    return next((a for a,b in zip("LR",sample) if not b),"-")

def one(plant,branch,mode,policy):
    m=plant(branch); q=Queue()
    try:
        if mode in ("sampled","skipped","late_retire"):
            # Once the effect occurs there is no future old action to fence.
            assert q.admit(lambda:m.old_attempt(0))
        retired=q.retire() if mode in ("retired","late_retire") else None
        taken=None if mode=="skipped" else m.local_sample(1)
        enclosed=q.state!="queued"
        act=policy(taken,enclosed)
        # Replays all orders at the same final commit cut. A later permit takes
        # effect in the native backend only if the queue still admits it.
        before=q.state
        q.admit(lambda:m.old_attempt(1))
        if q.state=="retired":m.idle_old_slot()
        delivered,independent,old_owed=m.commit(act,1)
        assert independent and old_owed
        effect_expected=int(mode!="retired")
        assert m.old_effects==effect_expected
        if retired is not None:
            assert retired==(mode=="retired")
        return {"sample":taken,"enclosed":enclosed,"retired":retired,"old_state_at_sample":before,
                "chosen":act,"old_effect_count":m.old_effects,
                "rescue":delivered,"independent":independent,"old_owed":old_owed}
    finally:
        m.close()

def best_from_selected_native_rows(alternatives):
    """Direct extensional nonanticipating policies, no choose() or closure rule."""
    information={}
    for (b,a),v in alternatives.items():
        information.setdefault((v["sample"],v["enclosed"]),set()).add(b)
    opt=[]
    for decisions in product(ACTIONS,repeat=len(information)):
        results=[]
        for (_,branches),a in zip(information.items(),decisions):
            results.extend(alternatives[b,a]["rescue"] for b in branches)
        opt.append(min(results))
    return max(opt)

def evaluate(plant):
    output={}
    for mode in MODES:
        selected={}
        for b,a in product("LR",ACTIONS):
            selected[b,a]=one(plant,b,mode,lambda _x,_y:a)
        observed={b:one(plant,b,mode,choose) for b in "LR"}
        for b,v in observed.items(): assert v==selected[b,v["chosen"]]
        best=best_from_selected_native_rows(selected)
        assert best==min(x["rescue"] for x in observed.values())
        assert best==int(mode in ("sampled","retired","late_retire"))
        if mode=="racing":
            # Passing both-clear observation does not reserve physical effect.
            assert all(observed[b]["sample"]==(0,0) for b in "LR")
            assert selected["L","L"]["rescue"]==0 and selected["R","R"]["rescue"]==0
        output[mode]={"observed":observed,"matched_direct_worst_case":best,
                      "fixed_rescue_by_branch":[[selected[b,a]["rescue"] for a in ACTIONS] for b in "LR"]}
    return output

def time_diagnostic(plant):
    """Post-freeze: do not transport a common expiration law between backends."""
    m=plant("L")
    try:
        m.old_attempt(0)
        assert m.local_sample(1)==(1,0)
        m.idle_old_slot()
        now=m.local_sample(1.25)
        outcome=m.commit("L",1.25)
        assert outcome[1:]==(1,1)
        return {"forced_side":"L","read_at_later_cut":now,"rescue":outcome[0]}
    finally:
        m.close()

a=evaluate(Warehouse)
b=evaluate(Network)
assert a==b
timing={m.__name__:time_diagnostic(m) for m in (Warehouse,Network)}
assert timing["Warehouse"]["rescue"]==0 and timing["Network"]["rescue"]==1
print(json.dumps({"same_typed_results_on_original_backends":True,
                  "frozen_runs_per_backend":40,"per_mode":a,
                  "later_single_site_diagnostic":timing},sort_keys=True,indent=2))
