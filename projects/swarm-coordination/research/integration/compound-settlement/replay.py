"""Source-derived readiness and settlement with the same cutoff checker."""
from itertools import product
import json
from pathlib import Path
import subprocess
import sys

from core import Cut,Old,decide
UP=Path(sys.argv[1])
sys.path.insert(0,str(UP.resolve()))
import rware_rotation as rw

class Warehouse:
    name='warehouse'

    def __init__(self):
        self.n=n=rw.engine(UP/"native_source.py")
        d=n.Direction
        positions=((1,0),(3,0),(2,2),(4,3))
        extra=((None,(0,4)),(None,(1,4)),(None,(2,4)),(None,(3,4)))
        self.w=rw.plant(n,positions,(d.DOWN,d.DOWN,d.UP,d.UP),
                        (*enumerate(positions),*extra),request=(0,1,2,3))
        self.w.np_random=rw.iso.NS(choice=lambda c:min((s for s in c if s.id>=5),key=lambda s:s.id))
        self.sites=((1,1),(3,1))
        self.w.goals=[*self.sites,(4,2)]
        for x,y in self.w.goals:
            self.w.highways[y,x]=True
        # Produce old preparation through native movement, then orient L.
        assert self.apply(0,0,1,0)==[0]*4
        assert self.pos(2)==(2,1)
        assert self.apply(0,0,n.Action.LEFT.value,0)==[0]*4
        assert self.w.agents[2].dir==d.LEFT
        self.first=0

    def pos(self,i):
        a=self.w.agents[i];return (a.x,a.y)

    def apply(self,*actions):
        _,pay,*_=self.n.step(self.w,actions)
        assert len({self.pos(i) for i in range(4)})==4
        return pay

    def pre(self,works):
        # Scoped authored first-actuator outage, not a RWARE fault detector.
        pay=self.apply(0,0,int(works),0)
        assert self.pos(2)==((1,1) if works else (2,1))
        self.first=int(pay[2]==.5)
        assert self.first==works
        self.was_success=bool(self.first)

    def evidence(self,at,mask):
        if mask:
            return Cut(Old.UNRESOLVED,(False,False))
        # Authored local enclosure of the completed first invocation. No
        # queue can execute this old attempt later; reward is actual delivery.
        # The read is of native grid occupancy, not of an intent label.
        free=tuple(bool(self.w.grid[0,y,x]==0) for x,y in self.sites)
        return Cut(Old.SETTLED if self.first else Old.LIVE,free)

    def commit(self,a,b,at):
        assert not (a==b and a!='-')
        assert not (a=='R' and self.first)
        if not self.first:
            for _ in range(2):
                pay=self.apply(0,0,self.n.Action.RIGHT.value,0)
                assert pay==[0]*4
            assert self.w.agents[2].dir==self.n.Direction.RIGHT
        pay=self.apply(int(b=='L'),int(b=='R'),int(a=='R'),1)
        old=self.first+int(pay[2]==.5)
        rescue=int(pay[0]==.5 or pay[1]==.5)
        independent=int(pay[3]==.5)
        if old:
            # Delivery does not discharge the separately required shelf return.
            assert self.w.agents[2].has_delivered and self.w.agents[2].carrying_shelf is self.w.shelfs[2]
        return (old,rescue,independent), {"return_owed":bool(old)}
    def close(self): pass

class Radio:
    name='radio'
    def __init__(self):
        self.p=subprocess.Popen([sys.argv[2]],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
        assert self.p.stdout.readline().split()==['prep','1','1']
    def call(self,phase,a,b,at):
        self.p.stdin.write(f"{phase} {a} {b} {at}\n"); self.p.stdin.flush()
        r=self.p.stdout.readline().split()
        assert len(r)==7 and r[0]==phase,r
        *base,self.arrivals=map(int,r[1:])
        return tuple(base)
    def pre(self,works):
        o,r,u,L,R=self.call('A','Y' if works else 'N','-',0)
        assert (o,r,u,L,R)==(int(works),0,0,3,0)
        self.first=o
    def evidence(self,at,mask):
        if mask:return Cut(Old.UNRESOLVED,(False,False))
        o,r,u,L,R=self.call('E','-','-',at)
        assert (r,u)==(0,0)
        # Local matched app callback + drained invocation, not over-air
        # notification. Measure the previous attempt's remaining native debit
        # from the source-stamped queue, using the documented matching cutoff.
        assert L in (0,3) and R==0
        return Cut(Old.SETTLED if o else Old.LIVE,(int(L)+3<=5,int(R)+3<=5))
    def commit(self,a,b,at):
        assert not (a==b and a!='-')
        assert not (a=='R' and self.first)
        o,r,u,L,R=self.call('C',a,b,at)
        assert 0<=o<=1 and u==1
        # The modeled delivery obligation ends at OldDock; report retention
        # at the sender is required through that native callback.
        return (o,r,u), {"retained_pending_copy":not bool(o)}
    def close(self):
        self.p.stdin.close();self.p.stdout.close();assert self.p.wait()==0

def run(plant,works,at,mask,actions=None):
    p=plant()
    try:
        p.pre(works)
        cut=p.evidence(at,mask)
        a,b=decide(cut) if actions is None else actions
        # Checker and direct comparator share authority. Masking retains a
        # reservation of BOTH unsettled permissions in this envelope.
        allowed= not (cut.old is Old.UNRESOLVED and (a,b)!=('-', '-'))
        allowed &= not (a=='R' and (cut.old is not Old.LIVE or not cut.usable[1]))
        allowed &= not (b!='-' and not cut.usable['LR'.index(b)])
        allowed &= not (a==b and a!='-')
        if not allowed:return None
        service,residual=p.commit(a,b,at)
        return cut,(a,b),service,residual
    finally:
        p.close()

def main():
    rows=[]
    for p,at,works,mask in product((Warehouse,Radio),(.75,1,1.25),(False,True),(False,True)):
        cut,action,service,res=run(p,works,at,mask)
        direct=[v[2] for a,b in product('-R','-LR')
                if (v:=run(p,works,at,mask,(a,b))) is not None]
        assert service==max(direct),(p.name,works,mask,at,service,direct)
        expected=(int(works),0,1) if mask else (1,int(works or p==Warehouse or at>1),1)
        assert service==expected,(p.name,works,mask,at,service,expected)
        rows.append(dict(plant=p.name,cut=at,first=works,witness_masked=mask,
              readiness=cut.usable,old=cut.old.name,chosen=action,service=service,residual=res,
              direct=max(direct)))
    # Bypass permission only in isolated simulation: test that a proposed
    # early residual attempt is blocked by the underlying native effect,
    # not merely by the checker filtering a choice.
    raw=[]
    for kind,at in product((Warehouse,Radio),(.75,1,1.25)):
        plant=kind()
        try:
            plant.pre(False)
            outcome,_=plant.commit('R','L',at)
            assert outcome==(1,int(kind is Warehouse or at>1),1)
            raw.append((kind.name,at,outcome))
        finally:
            plant.close()
    # Under lost acknowledgement the acting coordinator receives no old
    # settlement bit in either world. Test different placements of the
    # one-shot gate. RWARE's new adapter reads the actual native request
    # queue at the acting plant; SubT's sink may suppress an outcome only
    # after the source's actual attempted transmission.
    idempotent=[]
    for at,works in product((.75,1,1.25),(False,True)):
        p=Radio()
        try:
            p.pre(works)
            o,r,u,L,R=p.call('D','R','L',at)
            assert (o,r,u,R)==(1,int(at>1),1,3) and p.arrivals==1+int(works and at>1),(at,works,o,r,u,R,p.arrivals)
            idempotent.append(('radio_endpoint',at,works,(o,r,u),p.arrivals,R))
        finally:p.close()
        p=Warehouse()
        try:
            p.pre(works)
            # Local actual status; invoking guard elsewhere without matching
            # scope/evidence would be an unavailable control, not a baseline.
            live = p.w.shelfs[2] in p.w.request_queue
            assert live is not works
            (o,r,u),_=p.commit(*('R','L') if live else ('-','R'),at)
            assert (o,r,u)==(1,1,1)
            idempotent.append(('warehouse_effect_gate',at,works,(o,r,u),None,None))
        finally:p.close()
    fractured=[]
    for at,works,h in product((.75,1,1.25),(False,True),(0,1)):
        p=Radio()
        try:
            p.pre(works)
            o,r,u,L,R=p.call('F','R',str(h),at)
            assert (o,r,u)==(1,int(h==0 or at>1),1)
            fractured.append((at,works,h,(o,r,u),L,R))
        finally:p.close()
    split_checks=0
    for l,r,b,h in product(range(10),range(10),range(10),range(4)):
        direct=any(x+h<=l and b-x+h<=r for x in range(1,b))
        calc=2<=b and h<l and h<r and b+2*h<=l+r
        assert direct==calc
        split_checks+=1
    # Finite deterministic instance of the retained-conditional-reserve
    # equations. The 1/2 profile is an authored diagnostic sampling weight
    # across the existing runs, not a physical reliability model.
    from collections import Counter
    calibration={}
    for plant in ('warehouse','radio'):
        retained=[z for z in rows if z['plant']==plant and z['cut']==1 and not z['witness_masked']]
        full_joint=Counter((z['old'],z['readiness'][0]) for z in retained)
        all_reserve=Counter(z['readiness'][0] for z in retained)
        calibrated={}
        for status in ('LIVE','SETTLED'):
            old_marginal={str(r):n for (a,r),n in full_joint.items() if a==status}
            calibrated[status]=old_marginal
            assert len(old_marginal)==1
        reused_unconditional=(len(all_reserve)==1)
        assert reused_unconditional==(plant=='radio')
        calibration[plant]=dict(conditional_counts=calibrated,
                                reused_unconditional_is_calibrated=reused_unconditional)
    print(json.dumps(dict(rows=rows,plant_controls=raw,gate_placement=idempotent,
                         source_fiber_calibration=calibration,
                         segmented=fractured,split_exact_checks=split_checks,service_order=['old_delivery','rescue_delivery','independent'],
                         timing_not_a_clock_model=True),sort_keys=True,indent=2))
if __name__=='__main__':main()
