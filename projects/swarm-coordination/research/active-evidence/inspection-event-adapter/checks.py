from mission import Fixture,State,synth,execute
from itertools import product
import json

def seed(B=6,H=10,p_feed=False):
    def arc(id,a,b,d=1,sight=False):
        return {"id":id,"src":a,"dst":b,"dur":d,"cost":1,"local_visibility":sight}
    return {
      "start":"J","base":"base","start_epoch":2,"egress_due":H,
      "battery":50,"round_d":1,"send_cost":1,"round_limit":1,
      "all_in_round":True,"command_nodes":["J","P","Q"],"ack":True,
      "reports":[{"id":"A","deadline":B},{"id":"B","deadline":B}],
      "slots":[{"id":"r0","stock":["A"]},{"id":"r1","stock":["A","B"]},{"id":"r2","stock":["B"]}],
      "arcs":[arc("to-P","J","P"),arc("from-P","P","J"),
              arc("to-Q","J","Q",2),arc("from-Q","Q","J",2),
              arc("left","J","L"),arc("right","J","R"),
              arc("L-base","L","base",1,True),arc("R-base","R","base",1,True)],
      "probes":[{"id":"P","node":"P","dur":1,"cost":1,"fields":["exit","relay"],
                 "divert":[] if p_feed else ["r1"]},
                {"id":"Q","node":"Q","dur":1,"cost":1,"fields":["exit","relay"]}],
      "worlds":[
        {"arcs_down":{"L-base":[[2,20]]},"slots_down":{"r0":[[2,20]]},
         "signals":{"exit":"L","relay":"r0"}},
        {"arcs_down":{"R-base":[[2,20]]},"slots_down":{"r2":[[2,20]]},
         "signals":{"exit":"R","relay":"r2"}}
      ]}

def old_fixture():
    cases=0
    # Report and egress minima from #376 independent reference.
    for fed,D,H in product([False,True],[4,5,6],[7,8,9,10]):
        f=Fixture(seed(D,H,fed))
        policy=synth(f,extract=True)
        expected=(D>=5 and H>=8) if fed else (D>=6 and H>=10)
        assert bool(policy)==expected,(fed,D,H,policy)
        if policy:
            for i in range(len(f.worlds)):execute(f,i,policy)
        cases+=1
    print(cases,"#376 static-late-loss thresholds and actual trace replays")

def span_and_custody():
    b=seed(10,12)
    w=b["worlds"][0]
    w.setdefault("arcs_down",{})["to-Q"]=[[3,6]]
    w.setdefault("radio_down",{})["r1"]=[[3,5]]
    b["round_d"]=2;f=Fixture(b)
    start=f.initial(0)
    m=f.step(0,start,("move","to-Q"))
    assert m.busy_until==4 and m.loc=="J"
    assert f.step(0,m,("advance",)).failed # late closure during an admitted move
    def run(b):
        f=Fixture(b);s=f.initial(0)
        out=f.step(0,s,("send",(("A","r1"),("B","r2"))))
        return f.step(0,out,("advance",))
    out=run(b)
    assert dict(out.delivered)=={"B":4} and dict(out.receipts)=={"B":4}
    w["radio_down"]={"ack":[[3,5]]}
    out=run(b)
    assert dict(out.delivered)=={"A":4,"B":4} and not out.receipts
    # No valid received status even after actual delivery.
    w["absent_stock"]={"A":["r1"]}
    out=run(b)
    assert dict(out.delivered)=={"B":4} and not out.receipts
    # Fault starts exactly at the end, so prior effect has substantially
    # completed; changing ordering to before launch would change assignment.
    w["radio_down"]={"r1":[[4,5]]};del w["absent_stock"]
    assert len(run(b).delivered)==2
    # Force a second, late fault after first local actual probe.
    b=seed(9,12);b["round_d"]=2
    for w in b["worlds"]:w["radio_down"]={"r1":[[6,12]]}
    assert not synth(Fixture(b))
    print("mid-travel closure, mid-forward loss, missed ACK, missing copy, same-tick effects and second fault all checked")

if __name__=="__main__":
    old_fixture();span_and_custody()
    with open("base_fixture.json","w",encoding="utf8") as f:json.dump(seed(),f,indent=2);f.write("\n")
