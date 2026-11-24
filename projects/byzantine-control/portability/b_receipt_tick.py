# Run from projects/byzantine-control/portability under Python 3.12.
from fractions import Fraction as Q
import json
import rx_product as rx

def run(bank, delay, early_tick, a_late=Q(2), m_early=Q(3,2)):
    raw=rx.raw
    work=raw.SourceWork(2,2**40,2**32)
    lane=raw.RawLane(12*(6+2**98)+2,raw.LaneId(2,bank,0,1-bank),work)
    k=next(k for k,r in lane.records.items() if r.lifetime==512)
    r=lane.records[k]
    assert r.stage_receipt(441)=="staged" and r.service()=="receipt"
    for _ in range(511):
        assert r.start_tick()=="started" and r.service()=="tick"
    assert r.ttl==1 and r.readable()==441
    D=raw.RECORD_DELAY
    ticks={j:(Q(5001,5000),Q(5000,5001)) for j in lane.records}
    ticks[k]=(Q(5001,5000),D*(m_early if early_tick else 5))
    receiver=rx.Receiver(lane,rx.LanePhases((4096,Q(1,4096)-rx.SIGMA),None,ticks,{}))
    assert receiver.next_time()>0
    trace=[]
    def through(t):
        while receiver.next_time()<=t:
            receiver.now=receiver.next_time()
            for e in list(receiver.due()):
                outcome=receiver.act(e)
                trace.append([str(receiver.now/D),e[0],outcome,r.ttl])
        receiver.now=t
    staged_at=D*(a_late if delay else 0)
    through(staged_at)
    assert receiver.stage(k,913)=="staged"
    through(D*Q(13,4))
    on_time=lane.private_capture(k,r.role)
    alive_at_deadline=r.ttl
    through(D*4)
    eventually=lane.private_capture(k,r.role)
    assert work.stock+work.spent==2**32
    # Boundary calculation: an older running decrement occupies the same
    # commit aperture; a later tick cannot overtake a staged receipt.
    a=staged_at/D
    m=m_early if early_tick else Q(5)
    predicted=m+2 if m<a<m+1 else a+1
    actual=next(Q(t) for t,kind,outcome,_ in trace if outcome=="receipt")
    assert actual==predicted
    assert (on_time==913)==(predicted<=Q(13,4))
    return dict(bank=bank,delay=delay,early_tick=early_tick,
        on_time="unavailable" if on_time==raw.MASK else on_time,
        ttl=alive_at_deadline,eventually=eventually,trace=trace)

out=[run(bank,delay,tick) for bank in (0,1) for delay in (False,True) for tick in (False,True)]
assert [r["on_time"] for r in out]==([913,913,913,"unavailable"]*2)
assert all(r["eventually"]==913 for r in out)
perturbations=0
for a in (Q(19,10),Q(2),Q(21,10)):
    for m in (Q(14,10),Q(15,10),Q(16,10)):
        for b in (0,1):
            q=[run(b,d,e,a,m) for d in (False,True) for e in (False,True)]
            assert [row["on_time"] for row in q]==[913,913,913,"unavailable"]
            assert all(row["eventually"]==913 for row in q)
            perturbations+=1
print(json.dumps(dict(nominal=out,perturbed_four_arm_sets=perturbations)))
