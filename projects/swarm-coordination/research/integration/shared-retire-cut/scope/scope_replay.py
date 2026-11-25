from itertools import product
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from transfer import Warehouse,Network,ACTIONS

class WScope(Warehouse):
    def stage(self,z):
        actor=self.w.agents[2]
        actor.dir=self.n.Direction.LEFT if z=="L" else self.n.Direction.RIGHT
        actor.req_action=self.n.Action.FORWARD
        self.branch=z
    def footprint(self):
        a=self.w.agents[2]
        return "LR"[self.docks.index(a.req_location(self.w.grid_size))]
    def stage_transition(self,z):
        old=self.old_position()
        turn=self.footprint()!=z
        cmd=[0,0,self.n.Action.RIGHT.value if turn else 0,0]
        for _ in range(2):
            assert sum(self.n.step(self.w,cmd)[1])==0 and self.old_position()==old
        self.w.agents[2].req_action=self.n.Action.FORWARD
        self.branch=z
        assert self.footprint()==z
    def cancel(self): self.idle_old_slot()
    def execute(self): self.old_attempt(1)
    def service(self,a):
        r,u,o=self.commit(a,1)
        return r,u,self.old_effects,o

class NScope(Network):
    def evt(self,op,z="-"):
        self.p.stdin.write(f"{op} {z}\n");self.p.stdin.flush()
        row=self.p.stdout.readline().split()
        assert len(row)==5,row
        return row[0],tuple(map(int,row[1:]))
    def stage(self,z): self.evt("P",z)
    def footprint(self): return self.evt("F")[0]
    def cancel(self): self.evt("X")
    def execute(self): self.evt("O")
    def stage_transition(self,z):
        if self.footprint()!=z:
            self.evt("X");self.stage(z)
    def service(self,a): return self.evt("C",a)[1]

def shared(footprint, may_rebind):
    support=set("LR") if may_rebind else {footprint}
    return next((c for c in "LR" if c not in support),"-")

def one(backend, published, actual, cancel, plan, boundary=None):
    b=backend(published)
    try:
        b.stage(published)
        seen=b.footprint()
        assert seen==published
        cmd=plan(seen)
        b.stage_transition(actual)
        if boundary is not None:
            v=b.footprint()
            assert v==actual
            if boundary=="match":
                cancel|=v!=seen
            else:
                assert boundary=="refresh"
                cmd=plan(v)
        if cancel:
            b.cancel()
        else:
            b.execute()
        return b.service(cmd)
    finally:
        b.close()

def run(backend):
    rows={}
    for p,a in product("LR",repeat=2):
        for c in (False,True):
            for x in ACTIONS:
                rows[p,a,c,x]=one(backend,p,a,c,lambda _v:x)
    all_reports=[]
    for p in "LR":
        other="R" if p=="L" else "L"
        exact=one(backend,p,p,False,lambda s:shared(s,False))
        whole=one(backend,p,p,True,lambda s:shared(s,False))
        stale=one(backend,p,other,False,lambda s:shared(s,False))
        refuse=one(backend,p,other,False,lambda s:shared(s,True))
        assert exact==(1,1,1,1) and whole==(1,1,0,1)
        assert stale==refuse==(0,1,1,1)
        protected=one(backend,p,other,False,lambda s:shared(s,False),"match")
        refreshed=one(backend,p,other,False,lambda s:shared(s,False),"refresh")
        assert protected==(1,1,0,1) and refreshed==(1,1,1,1)
        # Lexicographic rescue, unrelated work, old progress, old unclosed.
        direct_bound=max(rows[p,p,c,x] for c,x in product((False,True),ACTIONS))
        assert direct_bound==exact
        # If old work is to remain authorized but can rebind, no guaranteed rescue.
        assert max(min(rows[p,a,False,x][0] for a in "LR") for x in ACTIONS)==0
        all_reports.append({"certified":exact,"retired":whole,"stale_scope":stale,
                            "conservative_rebinding":refuse,"protected":protected,
                            "refreshed":refreshed,"direct_bound":direct_bound})
    return all_reports

w=run(WScope)
r=run(NScope)
assert w==r
print(json.dumps({"outputs":["rescue","unrelated","old_progress","old_duty_owed"],
                  "native_runs_per_backend":36,"cases":w},sort_keys=True,indent=2))
