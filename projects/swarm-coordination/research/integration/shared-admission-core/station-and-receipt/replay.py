"""An actual ordered completion supplies a payload to a second native fixture."""
from itertools import product
from pathlib import Path
import subprocess
import sys
import types,json

up=Path(sys.argv[1])
sys.path.insert(0,str(up))
from core import Event, Use, Row, admitted

def load_warehouse():
    path=up/"partial.py"
    t=path.read_text()
    def sub(a,b):
        nonlocal t
        assert t.count(a)==1,a
        t=t.replace(a,b)
    sub("def native(arm, moved, read, cap, deadline):",
        "def native(arm, moved, read, cap, deadline, choose=lambda observation: False):")
    sub("        observed=content(buffer)\n",
        """        observed=content(buffer)
    early=choose(observed)
    staged=None
    if early:
        # Optional work acquires a real native item in a separate carrier,
        # and occupies one slot in the shared pickup audit. That source
        # action does not retire the old order.
        step(9,"stage optional item")
        aux=w.Carrier("aux")
        aux.receive_inventory([w.items[8]])
        pickups+=1
        staged=aux.report_inventory_item_names()
        assert staged==["item8"] and pickups<=cap
""")
    sub("enough=cap>=4-(observed==[4]) and deadline>=12",
        "enough=cap>=4-(observed==[4])+early and deadline>=12")
    sub("return dict(arm=arm,moved=moved,read=read,cap=cap,deadline=deadline,picks=pickups,",
        """return dict(arm=arm,moved=moved,read=read,cap=cap,deadline=deadline,picks=pickups,
                native_old=[v for v in wire if v["command"]=="ORDERCOMPLETE"],
                staged=staged,chosen_early=early,
""")
    ns=types.ModuleType("partial_extension")
    exec(compile(t,str(path),"exec"),ns.__dict__)
    return ns

def row(moved,visible,pick_cap,radio_cap,optional):
    # Source, not control, supplies actual existence; the receiver uses
    # only the local view. Upcoming stock callback requires physical
    # settlement and its own separate receive debit in the same branch.
    ages=((9,"dispatch",moved),) if visible else ()
    facts=frozenset({("buffer",4)}) if moved else frozenset()
    K=("pick",); R=("Base-rx",)
    def pick(at,ord):
        return Event(at,ord,uses=(Use(K,1,pick_cap,13),))
    prior=(pick(5,0),pick(6,0))
    menu={}
    for use,early in product(("reuse","repick"),(False,True)):
        trail=[pick(10,0),Event(12,0,paid=("old-station",)),
               Event(12,1,paid=("separate-unload",)),
               Event(13,0,uses=(Use(R,173,radio_cap,4),),paid=("old-receipt",))]
        if use=="repick":trail.append(pick(11,0))
        else:trail.append(Event(11,0,need=frozenset({("buffer",4)})))
        if early:
            trail.extend([pick(9,0),Event(11,1,uses=(Use(R,60,radio_cap,4),),
                                             paid=("optional",) if optional else ())])
        menu[use,early]=tuple(trail)
    return Row(ages,facts,prior,menu)

def selector(visible,P,C):
    actions=tuple(product(("reuse","repick"),(False,True)))
    dues={"old-station":12,"separate-unload":12,"old-receipt":13}
    baseline=admitted([row(b,visible,P,C,False) for b in (False,True)],
                      "dispatch",9,dues,actions)
    optional=admitted([row(b,visible,P,C,True) for b in (False,True)],
                      "dispatch",9,dues|{"optional":11},actions)
    out={}
    for view in baseline:
        worlds=tuple(b for b in (False,True) if not view or b==view[0][1])
        ok=tuple((use,early) for use,early in actions if
          (use=="repick" or all(worlds)) and
          3+int(use=="repick")+int(early)<=P and 173+60*early<=C)
        assert baseline[view]==ok
        assert optional[view]==tuple(x for x in ok if x[1])
        out[view]=bool(optional[view])
    return out

def body(value,n):
    v=json.dumps(value,sort_keys=True,separators=(",",":")).encode()
    assert len(v)<=n
    return v.ljust(n,b" ").hex()

def main():
    w=load_warehouse()
    runner=subprocess.Popen([sys.argv[2]],text=True,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def ask(x):
        runner.stdin.write(x+"\n");runner.stdin.flush()
        return runner.stdout.readline().strip()
    rows=[]
    for j,(m,read,P,C,arm) in enumerate(product((False,True),(False,True),
               (3,4,5),(173,200,232,233),("combined","picks-only","radio-only"))):
        menu=selector(read,P,C)
        def choose(observed):
            v=((9,observed==[4]),) if observed is not None else ()
            if arm=="combined":return menu[v]
            if arm=="picks-only":return P>=4+int(observed!=[4])
            return C>=233
        h=w.native("buffer",m,read,P,12,choose)
        early=h["chosen_early"]
        assert early==choose([4] if m and read else [] if read else None)
        assert h["picks"]<=P and h["side"]
        assert h["settled"]==(P>=4-int(read and m)+int(early))
        assert ask("reset "+str(C))=="ok"
        if h["staged"]:
            side=ask(f"send 11 Q {body(dict(ep=j,item=h['staged']),60)}")
            assert side=="1 60 60"
        else:
            assert not early
        receipt=h["native_old"]
        assert len(receipt)==int(h["settled"])
        if receipt:
            msg=receipt[0]
            assert msg["command"]=="ORDERCOMPLETE" and msg["objName"]=="order1"
            old=ask(f"send 13 P {body(dict(ep=j,result=msg),173)}").split()
            oldok=bool(int(old[0]))
            assert oldok==(C>=173+60*early)
            assert list(map(int,old[1:]))==[173,60*early+173*oldok]
            # It follows that even a capacity-blocked old receive costs
            # the already admissible sender debit.
        else:
            oldok=False
        assert (not early or oldok or arm!="combined")
        rows.append(dict(ep=j,arm=arm,available=m,read=read,picks=P,rx=C,
                         staged=early,station=h["settled"],received=oldok,side=h["side"]))
    runner.stdin.close()
    assert runner.wait()==0
    positive=[r for r in rows if r["arm"]=="combined" and r["picks"]>=4]
    assert all(r["station"] and r["received"] and r["side"] for r in positive)
    loses_transport=[r for r in rows if r["arm"]=="picks-only" and r["station"] and not r["received"]]
    loses_station=[r for r in rows if r["arm"]=="radio-only" and r["staged"] and not r["station"]]
    summary=dict(verified_old_jobs=len(positive),early_joint=sum(r["staged"] for r in positive),
                 one_layer_misses_receipt=len(loses_transport),one_layer_misses_station=len(loses_station))
    assert summary==dict(verified_old_jobs=32,early_joint=5,
                        one_layer_misses_receipt=15,one_layer_misses_station=7)
    print(json.dumps(dict(principal=rows,summary=summary),sort_keys=True,indent=2))

if __name__=="__main__":main()
