"""Native warehouse cut -> actual broker callback -> two-turn deadline."""
from contextlib import closing
from itertools import product
from pathlib import Path
import json
import subprocess
import tempfile
from durable_asof import create,prefix,evidence,authorized_turn,reconstruct,conn
from same_queue import move,A

def frame(r):
    origin,t,previous,assigned=r
    assert origin=="station-A:era-1" and 0<t<100 and 0<previous<10 and 0<assigned<10
    return f"A{t:02}{previous}{assigned}"
def receipt(s):
    assert s[0]=="A" and len(s)==5
    return "station-A:era-1",int(s[1:3]),int(s[3]),int(s[4])

def oracle(cap,events):
    sent={who:[] for who in "PQS"}; heard=[]; good=[]
    # Independent exact per-sender and receiver windows on integer ticks.
    for t,who,data in events:
        m=len(data)
        if sum(n for e,n in sent[who] if t-e<=16)+m>cap:good.append("-");continue
        sent[who].append((t,m))
        if sum(n for e,n in heard if t-e<=16)+m>cap:good.append("-");continue
        heard.append((t,m));good.append(data)
    return good

def main():
    fixtures={}
    queries=[]
    with tempfile.TemporaryDirectory() as p:
      for seed,pose in product((14,9),(2,4)):
        db=Path(p)/f"{seed}.{pose}.db";create(db,seed,pose);prefix(db,"none")
        cur,probe,older=evidence(db,15);_,_,latest=evidence(db,15,"latest")
        assert older[1]==1 and latest[1]==15 and cur[2]==(4,)
        a,b=frame(older),frame(latest)
        old="OK"+str(cur[2][0])  # actual second native delivery's new requested ID
        P=(15,"P",a);Q=(15,"Q",old);S=(15,"S",b)
        cases={"typed":[P,Q],"latest-only":[S,Q],"rush":[S,P,Q],
          "exact-expiry":[P,Q,(31,"S",b)],"defer":[P,Q,(32,"S",b)],
          "bad-retry":[P,Q,(31,"S",b),(32,"S",b)],
          "late-proof":[Q,(16,"P",a)]}
        fixtures[seed,pose]=(db,cur,probe,a,b,old)
        for cap,(name,events) in product(range(6,15),cases.items()):
            queries.append(((seed,pose),cap,name,events))
      lines=[]
      for _,cap,_,events in queries:
        lines.append(f"{cap} {len(events)}")
        lines.extend(f"{t} {s} {data}" for t,s,data in events)
      rr=subprocess.run(["./deliver"],input="\n".join(lines)+"\n",text=True,capture_output=True)
      assert rr.returncode==0,rr.stderr
      stdout=rr.stdout.splitlines()
      assert len(stdout)==len(queries)
      keyout={}; accepted=0; native_moves=0
      for (k,c,name,events),row in zip(queries,stdout):
        db,cur,probe,a,b,old=fixtures[k]
        fields=row.split()
        assert int(fields[0])==len(events)
        data=fields[1:]
        assert data==oracle(c,events)
        got=[msg for msg,(t,_,_) in zip(data,events) if t<=15 and msg!="-"]
        options=[authorized_turn(cur,probe,receipt(x)) for x in got if x.startswith("A")]
        turns={o for o in options if o is not None}
        assert len(turns)<=1
        turn=next(iter(turns)) if turns else None
        old_delivered=old in got
        latest_delivered=b in data
        if turn:
            assert turn==("LEFT" if k[1]==2 else "RIGHT")
            # Open native plant only after the actual receiver had the binding.
            with closing(conn(db)) as co:w,_=reconstruct(co)
            move(w,a=A[turn]);move(w,a=A.FORWARD)
            assert (w.agents[0].x,w.agents[0].y,w._cur_steps)==(3,3,17)
            native_moves+=2
        else:
            # Correctly refuses this branch; no infeasible rescue is credited.
            assert a not in got
        good=bool(turn) and old_delivered
        control=(old_delivered,bool(turn),latest_delivered,good)
        if (c,name) in keyout:assert keyout[c,name]==control
        keyout[c,name]=control
        accepted+=good
      for c in range(6,15):
        assert keyout[c,"typed"]==(True,True,False,True) if c>=8 else (not keyout[c,"typed"][3])
        assert keyout[c,"late-proof"][:2]==(True,False)
        assert not keyout[c,"latest-only"][1]
        assert keyout[c,"rush"][3]==(c>=13)
        assert keyout[c,"defer"][3]==(c>=8) and keyout[c,"defer"][2]
        assert keyout[c,"exact-expiry"][2]==(c>=13)
      assert keyout[8,"rush"]==(True,False,True,False)
      assert keyout[10,"rush"]==(False,True,True,False)
      assert keyout[8,"bad-retry"]==(True,True,False,True)
      assert keyout[10,"bad-retry"]==(True,True,True,True)
      print(json.dumps({"cases":len(queries),"joint_deadlines_met":accepted,"native_suffix_actions":native_moves,
            "each_cell":[[c,n,*k] for (c,n),k in sorted(keyout.items())]},sort_keys=True,separators=(",",":")))
if __name__=="__main__":main()
