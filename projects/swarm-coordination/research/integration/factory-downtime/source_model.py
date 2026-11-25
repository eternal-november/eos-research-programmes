"""Discrete civil factory model with explicit custody and source event order."""
from dataclasses import dataclass,replace
from itertools import product

@dataclass
class Machine:
    name: str
    locked: int=0
    job: str|None=None
    work: int=0
    pickup: int=0
    done: bool=False
    def install(self, t, job, work, handling):
        assert t>=self.locked and self.job is None and work>0
        self.job,self.work,self.pickup,self.done=job,work,handling,False
    def progress(self,t,log):
        # Time elapses from t to t+1. No completion can authorize
        # a material handoff merely by taking the last processing tick.
        if t<self.locked or self.job is None:return
        if self.work:
            self.work-=1
            if not self.work:
                self.done=True
                log.append((t+1,self.name,"machine-ready",self.job))
        elif self.pickup:
            self.pickup-=1
    def fault(self,t,length,kind,log):
        assert length>=0 and kind in ('pause','remove')
        self.locked=max(self.locked,t+length)
        log.append((t,self.name,kind,self.job))
        if kind=='remove' and self.job is not None:
            log.append((t,self.name,'resident-removed',self.job))
            self.job=None; self.work=self.pickup=0; self.done=False
    def collect(self,t,log,custody):
        if self.job is not None and t>=self.locked and self.done and not self.pickup:
            # Custody/collection, not machine-ready, commits the product.
            custody.add(self.job)
            log.append((t,self.name,'secured',self.job))
            self.job=None; self.work=self.pickup=0; self.done=False

@dataclass(frozen=True)
class Fixture:
    x_fault: str
    y_fault: str
    x_down: int=30
    y_cut: int=30
    y_down: int=30
    first_work: int=27
    first_handle: int=2
    old_remaining: int=24
    later_work: int=24
    later_handle: int=1
    deadline: int=60
    before_fault: bool=False

def replay(w, first, launch=0):
    assert 0<=launch<w.y_cut and first in ('P','Q')
    X=Machine('X',job='P',work=w.old_remaining,pickup=w.later_handle)
    Y=Machine('Y')
    custody=set();log=[]
    for t in range(w.deadline+1):
        if w.before_fault:
            X.collect(t,log,custody);Y.collect(t,log,custody)
        if not t:X.fault(0,w.x_down,w.x_fault,log)
        if t==w.y_cut:Y.fault(t,w.y_down,w.y_fault,log)
        X.collect(t,log,custody);Y.collect(t,log,custody)
        if t==w.x_down and w.x_fault=='remove':
            X.install(t,'Q',w.later_work,w.later_handle)
            log.append((t,'X','new-start','Q'))
        if t==launch:
            Y.install(t,first,w.first_work,w.first_handle)
            log.append((t,'Y','new-start',first))
        if t<w.deadline:
            X.progress(t,log);Y.progress(t,log)
    return frozenset(custody),tuple(log)

def closed(w,first,launch=0):
    # Independent timing model: active occupancy is work + declared handling.
    # Scheduled downtime pauses both in this test; a referee removal
    # destroys even a finished item still on the output conveyor.
    out=set()
    xj,xr=('P',w.old_remaining) if w.x_fault=='pause' else ('Q',w.later_work)
    if w.x_down+xr+w.later_handle<=w.deadline:out.add(xj)
    end=launch+w.first_work+w.first_handle
    e_before=end<w.y_cut or (end==w.y_cut and w.before_fault)
    if e_before and end<=w.deadline:
        out.add(first)
    if not e_before and w.y_fault=='pause' and end+w.y_down<=w.deadline:
        out.add(first)
    return frozenset(out)

def feasible(worlds,lag):
    return {j for j in 'PQ' if all(replay(w,j,lag)[0]=={'P','Q'} for w in worlds)}

def main():
    p=Fixture('pause','pause')
    q=Fixture('remove','pause')
    assert feasible((p,),0)=={'Q'} and feasible((q,),0)=={'P'}
    assert not feasible((p,q),0)
    assert all(feasible((w,),1) for w in (p,q)) # Y resumes and collects exactly at 60
    assert not any(feasible((replace(w,deadline=59),),1) for w in (p,q))
    good,trace=replay(p,'Q')
    assert (27,'Y','machine-ready','Q') in trace
    assert (29,'Y','secured','Q') in trace
    border=Fixture('pause','remove',first_work=28)
    at,events=replay(border,'Q')
    assert at=={'P'} and (28,'Y','machine-ready','Q') in events
    assert (30,'Y','resident-removed','Q') in events
    assert replay(replace(border,before_fault=True),'Q')[0]=={'P','Q'}
    count=0
    for y,xf,yf,xd,yd,fw,fh,ox,lw,lh,dead,ef,start in product(
        (29,30,31),('pause','remove'),('pause','remove'),(30,60),(30,60),
        (25,29,30),(0,1,3),(20,30),(20,30),(0,1),(59,60,89),(False,True),(0,2)):
        if y>dead:continue
        w=Fixture(xf,yf,xd,y,yd,fw,fh,ox,lw,lh,dead,ef)
        for k in 'PQ':
            assert replay(w,k,start)[0]==closed(w,k,start),(w,k,start)
            count+=1
    print(count,'actual custody effect histories agree with the independent interval calculation')
    print('same DOWN-only view, both singleton modes feasible but no robust common first act')
    print('a one-tick delayed report with a paused alternate collects at 60, not by 59')
    print('machine-ready at 28; destructive removal before collection at 30 loses the item')
if __name__=='__main__':main()
