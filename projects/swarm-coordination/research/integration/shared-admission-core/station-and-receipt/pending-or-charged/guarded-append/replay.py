"""Deterministic research fixture: normal dispatch can interleave preparation and commit."""
from itertools import product
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from joined import body, load_warehouse

def oracle(cap, transition, fanout, at, removable, arm):
    pending=transition=="blocked"
    live=60*fanout*(not pending and at<=6)
    charged=60*fanout
    if arm=="optimistic":
        send="Q" if cap>=233 or removable and cap>=173 else "R"
        remove=pending and cap<233 and removable and cap>=173
    else:
        count=1 if arm=="one-entry" else fanout
        cost=60*count*pending
        send="Q" if cap>=live+cost+173 else "R"
        remove=send=="R" and pending and removable and cap>=live+173
        if remove:send="Q"
    if cap<173:return "-",False,False
    return send,remove,send=="R" or live+charged*(pending and not remove)+173<=cap

def main():
    warehouse=load_warehouse()
    old=warehouse.native("buffer",True,True,3,12)
    assert len(old["native_old"])==1 and old["settled"]
    report=body(dict(ep=33,result=old["native_old"][0]),173)
    probe=body(dict(k="probe"),60)
    side=body({"i":4},10)
    with subprocess.Popen([str(Path(sys.argv[2]).resolve())],text=True,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL) as p:
      def ask(*args):
        p.stdin.write(" ".join(map(str,args))+"\n");p.stdin.flush()
        return p.stdout.readline().strip().split()
      def cmd(ok,*args):
        got=ask(*args)
        assert got==ok,(args,got,ok)
      def run(cap,event,fanout,at,remove_permission,append_late,arm):
        cmd(["ok"],"reset",cap)
        if fanout==2:cmd(["ok"],"fanout")
        cmd(["ok"],"enqueue","Q","Side",probe)
        cmd(["1"],"pending","Q","Side",probe)
        cmd(["0"],"tx",0,"Q")
        # The early snapshot is genuine. Dispatch at tick 2 can leave
        # it unchanged or consume the probe, even without delivery.
        d=ask("dispatch",2,int(event!="blocked"),int(event=="received"))
        assert d==(["0"] if event!="received" else [str(fanout)]+["Q:60"]*fanout)
        cmd(["ok"],"enqueue","Side","Independent",side)
        if arm=="optimistic":
            sender="Q" if cap>=233 or remove_permission else "R"
            removed=remove_permission and cap<233 and cap>=173 and                     ask("remove","Q","Side",probe)==["1"]
            if cap<173:sender="-"
            else:cmd(["ok"],"enqueue",sender,"Base",report)
            actual_cost=None
        else:
            sender,rm,l,q=ask("commit",cap,at,1,remove_permission,int(arm=="prefix"),probe,report)
            removed=rm=="1"; actual_cost=[int(l),int(q)]
            assert actual_cost==([fanout*(event!="blocked"),1+int(event=="blocked")]
                                if cap>=173 else [0,0]),actual_cost
        if append_late:cmd(["ok"],"enqueue","Q","Side",probe)
        out=ask("dispatch",at,1,1)
        assert out.count("Side:10")==1
        received=sender+":173" in out
        assert (sender,removed,received)==oracle(cap,event,fanout,at,remove_permission,arm),(
            cap,event,fanout,at,remove_permission,arm,out)
        return sender,removed,received,actual_cost
      rows=[]
      for case in product((172,173,232,233,292,293),("blocked","erased","received"),
                          (1,2),(4,6,7),(False,True),(False,True),
                          ("optimistic","one-entry","prefix")):
        # Integers passed to the C++ read seam are literal 0/1.
        x=tuple(int(v) if isinstance(v,bool) else v for v in case)
        rows.append([*case,*run(*x)])
      assert len(rows)==1296
      summary={}
      for arm in ("optimistic","one-entry","prefix"):
        viable=[r for r in rows if r[6]==arm and r[0]>=173]
        summary[arm]=[len(viable),sum(r[-2] for r in viable),
                      sum(r[-4]=="R" for r in viable),sum(r[-3] for r in viable)]
      assert summary["prefix"][0]==summary["prefix"][1]
      assert all(s[0]>s[1] for k,s in summary.items() if k!="prefix")
      p.stdin.close(); assert p.wait()==0
    encoded=json.dumps(rows,separators=(",",":")).encode()
    witnesses=[r for r in rows if r[:6] in (
      [232,"erased",1,4,True,False],
      [292,"blocked",2,4,True,True],
      [293,"blocked",2,4,True,True])]
    out=dict(rows=len(rows),sha256=hashlib.sha256(encoded).hexdigest(),
             summary=summary,witnesses=witnesses)
    if "--full" in sys.argv:out["cases"]=rows
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=="__main__":main()
