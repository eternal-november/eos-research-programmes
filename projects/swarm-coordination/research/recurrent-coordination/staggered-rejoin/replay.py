"""Warehouse recurrence with delayed local topology notices and durable dock custody."""
from collections import defaultdict
from itertools import product
import hashlib
import json
from pathlib import Path
from escrow_source import Warehouse, View, ID, expand

ACTORS="AB"
PREVIEW_DIGEST="a537e62b1189fbfa9789623c07966bba030e787125221bb30530b21009d1b47d"
assert hashlib.sha256(Path(__file__).with_name("escrow_source.py").read_bytes()).hexdigest()==PREVIEW_DIGEST

def other(i):
    return ACTORS[1-ACTORS.index(i)]

def replay(plans,P=4,Q=2,h=2,L=2,policy=True,stale=True,late_switch=None):
    """plans: (onset, actual-up, buyer or None, notice delays A,B).
    Plant handles epoch checking; local controllers do not read actual epoch."""
    w=Warehouse(dict(p="A",a="A",b="B"))
    agenda={}
    for e,(t,up,buyer,ds) in enumerate(plans,1):
        assert up==(buyer in ACTORS if buyer is not None else False)
        agenda[t]=(e,up,buyer)
    horizon=plans[-1][0]+max(plans[-1][3])+L+h+2*P+Q+2
    physical=(0,False,None)
    knowledge={i:(0,False,None) for i in ACTORS}
    requests={i:None for i in ACTORS}
    noticeq=defaultdict(list)
    wire=defaultdict(list)
    dock=defaultdict(list)
    settles=defaultdict(list)
    receipts=defaultdict(list)
    gate_used=False
    services={}
    by_grant={}
    traces=[]
    authority_seq=defaultdict(int)
    replica={i:View() for i in ACTORS}
    raw_seen={i:set() for i in ACTORS}
    raw_retired={i:set() for i in ACTORS}
    previous=View()
    high_width=0
    def publish(i,g,r=None):
        replica[i].grant(w,g,"bundled")
        raw_seen[i].update(ID(g.id.issuer,n) for n in range(1,g.id.n+1))
        raw_seen[i].update(expand(g.cumulative))
        raw_retired[i].update(expand(g.cumulative))
        if r is not None:
            assert replica[i].receipt(w,r)
            raw_retired[i].add(r.id)
    def tr(t,label,*v):
        traces.append([t,label,*v])
    def start(t,i,right,e=None):
        nonlocal gate_used
        g=w.issue(i,right)
        settles[t+P].append(g)
        by_grant[g.id]=(t,i,right,e)
        if right=="p":
            gate_used=True
        publish(i,g)
        tr(t,"start",i,right,g.id.n,e)
    def own(i): return "p" in w.locals[i]
    def gate(e,i): return physical==(e,True,i) and not gate_used
    def rd(i,r):
        own_ready=all(replica[i].F.get(j,0)>=n for j,n in w.locals[i][r])
        assert own_ready==w.ready(i,r)
        return own_ready
    def change(t):
        nonlocal physical,gate_used
        physical=agenda[t]
        gate_used=False
        e,up,buyer=physical
        for i,delta in zip(ACTORS,plans[e-1][3]):
            assert t!=late_switch or delta>0
            noticeq[t+delta].append((i,physical))
        tr(t,"link_change",e,up,buyer)
    for t in range(horizon+1):
        for g in settles.pop(t,[]):
            r=w.settle(g)
            receipts[t+Q].extend((i,r,g) for i in ACTORS)
            s,i,right,e=by_grant[g.id]
            tr(t,"rack_accepts",i,right,g.id.n,e)
            if e is not None:
                services[e]=(s,t)
        # Deliver the cap-valid grant and receipt together so the learned facts
        # are exact at this publication cut. Custody never follows a receipt.
        for i,r,g in receipts.pop(t,[]):
            w.learn(i,r)
            publish(i,g,r)
        if t in agenda and t!=late_switch:
            change(t)
        for i,p in noticeq.pop(t,[]):
            e,up,buyer=p
            if e<=knowledge[i][0]:
                tr(t,"old_notice_rejected",i,e)
                continue
            knowledge[i]=p
            tr(t,"noticed",i,e,up,buyer)
            if i==buyer and up:
                tr(t,"ask",i,e)
                # Physical ingress below the policy: a disconnected link
                # passes no new payload. Previously delivered items may
                # wait unread in the receiver mailbox across the split.
                if physical[1]:
                    wire[t+L].append((other(i),e,i))
                    if stale:
                        wire[t+L+7].append((other(i),e,i))
                else:
                    tr(t,"link_drops_request",i,e)
        for i,e,buyer in wire.pop(t,[]):
            # The physical link may hold an old authenticated message across
            # changes; delivery is not admission. Keep only the newest request.
            prev=requests[i]
            if e<knowledge[i][0] or (prev is not None and e<=prev[0]):
                tr(t,"old_request_filtered",i,e)
            else:
                requests[i]=(e,buyer)
                tr(t,"request_received",i,e)
        for i,token in dock.pop(t,[]):
            w.receive_right(i,token)
            tr(t,"take_right",i,token.generation)
            if t>0:
                try:
                    w.receive_right(i,token)
                    raise AssertionError("duplicate must not move authority")
                except ValueError:
                    pass
        # Decisions read only each own observed epoch, request, ready/owned.
        for i in ACTORS:
            e,up,buyer=knowledge[i]
            if policy and own(i) and up and buyer!=i and requests[i]==(e,buyer):
                if gate(e,buyer):
                    token=w.send_right(i,buyer,"p")
                    dock[t+h].append((buyer,token))
                    tr(t,"deposit_right",i,buyer,e,token.generation)
                else:
                    tr(t,"stale_deposit_refused",i,e)
                requests[i]=None
            if own(i) and up and buyer==i and rd(i,"p") and authority_seq[i]<e:
                if gate(e,i):
                    start(t,i,"p",e)
                else:
                    tr(t,"stale_start_refused",i,e)
                authority_seq[i]=e
        for i in ACTORS:
            right=i.lower()
            if rd(i,right):
                start(t,i,right)
        if t==late_switch:
            change(t)
        w.invariant()
        v=replica["A"].join(replica["B"])
        assert v.width()<=3
        high_width=max(high_width,v.width())
        assert v.S==raw_retired["A"]|raw_retired["B"]
        seen=raw_seen["A"]|raw_seen["B"]
        assert all(v.query(j)==('settled' if j in v.S else 'awaiting' if j in seen else 'unknown')
                   for j in by_grant)
        assert replica["A"].join(replica["B"].join(previous)).report()==v.join(previous).report()
        previous=v
    return dict(trace=traces,service=services,maximum_join_width=high_width)

def lower_bound_reference(delta_a,delta_b,L,h,P,Q,old_busy,old_release,evidence,initial_owner,buyer,remaining_mail=0):
    """Independent solution of enabling inequalities at a stable rejoin.
    Old pooled migration, if in flight, arrives to initial_owner after remaining_mail.
    Required prefix evidence can already be held, or only available at evidence."""
    b_notice=delta_a if buyer=="A" else delta_b
    o_notice=delta_a if initial_owner=="A" else delta_b
    if initial_owner==buyer:
        custody=remaining_mail
    else:
        custody=max(remaining_mail,o_notice,b_notice+L)+h
    return max(b_notice,custody,old_release if old_busy else 0,evidence)+P

def launch_model(da,db,L,h,P,release,evidence,owner,buyer,R):
    """Small stable-window event interpreter; controls see local signals only.
    Supplies an old duty already admitted on the dock and known prefix barrier."""
    e=1
    custody=None if R else owner
    seen={i:False for i in ACTORS}
    req=False
    offered=False
    req_at=None
    deposit_at=None
    physical_active=release>0
    learned=False
    for t in range(60):
        if t==release:
            physical_active=False
        if t==evidence:
            learned=True
        for i,d in zip(ACTORS,(da,db)):
            if d==t:
                seen[i]=True
        if seen[buyer] and not offered:
            req_at=t+L
            offered=True
        if t==req_at:
            req=True
        if R and t==R:
            assert custody is None
            custody=owner
        if t==deposit_at:
            assert custody is None
            custody=buyer
        if custody==other(buyer) and seen[custody] and req:
            custody=None
            deposit_at=t+h
        if custody==buyer and seen[buyer] and learned:
            assert not physical_active
            return t+P
    raise AssertionError("horizon")

def main():
    # Earliest legal finish independent of notification order and certificate phase.
    sweeps=0
    for da,db,L,h,P,release,Q,owner,buyer,R in product(range(4),range(4),range(1,4),range(1,4),
            range(1,4),range(4),range(4),ACTORS,ACTORS,range(4)):
        ev=release+Q
        x=launch_model(da,db,L,h,P,release,ev,owner,buyer,R)
        assert x==lower_bound_reference(da,db,L,h,P,Q,release>0,release,ev,owner,buyer,R)
        sweeps+=1
    # Cross-check complete event simulator in the stable fresh-input subfamily.
    cross=0
    for da,db,L,h,P,Q,buyer in product(range(3),range(3),range(1,3),range(1,3),
            range(1,3),range(1,3),ACTORS):
        full=replay([(0,True,buyer,(da,db))],P=P,Q=Q,h=h,L=L,stale=False)
        assert full["service"][1][1]==lower_bound_reference(da,db,L,h,P,Q,False,0,0,"A",buyer)
        cross+=1
    plans=[(0,True,"A",(0,2)),(1,False,None,(3,1)),(3,True,"B",(1,0)),
           (5,False,None,(2,1)),(7,True,"B",(2,1)),(8,False,None,(4,2)),
           (10,True,"A",(1,4)),(22,False,None,(2,1)),(23,True,"B",(0,1)),
           (28,False,None,(3,2)),(30,True,"B",(2,0)),(45,False,None,(2,1)),
           (46,True,"A",(2,0))]
    r=replay(plans)
    events=r["trace"]
    # No common reset and physical old private and pooled duties remain.
    assert all(sum(v[1]=="start" and v[2]==i and v[3]==i.lower() for v in events)>=5 for i in ACTORS)
    assert any(v[1]=="old_notice_rejected" for v in events)
    assert any(v[1]=="old_request_filtered" for v in events)
    assert any(v[1].startswith("stale_") and v[1].endswith("refused") for v in events)
    assert len(r["service"])>=3
    assert [26,"deposit_right","A","B",9,1] in events
    assert [28,"link_change",10,False,None] in events and [28,"take_right","B",1] in events
    assert r["service"][11]==(30,34) and 9 not in r["service"]
    assert any(any(v[1]=="link_change" and s<v[0]<d for v in events) for s,d in r["service"].values())
    # Event-order control: moving physical split earlier rejects that episode's
    # optional pooled service, but does not retroactively cancel a prior start.
    order=[(0,True,"A",(1,1)),(1,False,None,(2,1)),(9,True,"B",(0,0))]
    preserve=replay(order,late_switch=1)
    forbid=replay(order)
    assert preserve["service"][1]==(1,5) and 1 not in forbid["service"]
    assert any(v==[1,"stale_start_refused","A",1] for v in forbid["trace"])
    print(json.dumps(dict(stable_reference_comparisons=sweeps,full_reference_comparisons=cross,recurrence=r,
          order_control={"accepted_before_split":preserve["service"],"noticed_after_split":forbid["service"]}),sort_keys=True,indent=1))

if __name__=="__main__": main()
