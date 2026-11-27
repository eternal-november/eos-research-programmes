"""Native queue/effect comparison, deterministic fixture; controls are authored."""
from itertools import product
import json
from pathlib import Path
import subprocess
import sys
from joined import body, load_warehouse

def direct(cap, switched, ready, at, prior, rule):
    # Rolling-window component is an independent, closed-form comparator.
    source='P' if not switched else 'Q' if ready else 'R'
    if cap<173:
        return (source,False,False)
    if rule=="source-qualified" and source=='Q' and cap<233:
        if prior!='pending' and at<=4:
            source='R'
    if rule=="uniform-fallback" and source=='Q' and cap<233:
        source='R'
    remove=rule=="source-qualified" and source=='Q' and cap<233 and prior=='pending'
    charged=(source=='Q' and
             ((prior=='pending' and not remove) or (prior!='pending' and at<=4)))
    return source,remove,cap>=173+60*charged

def main():
    w=load_warehouse()
    native=w.native("buffer",True,True,3,12)
    no_receipt=w.native("buffer",False,False,3,12)
    assert no_receipt["native_old"]==[] and len(native["native_old"])==1
    receipt=body(dict(ep=4,result=native["native_old"][0]),173)
    diag=body(dict(ep=4,kind="optional"),60)
    unrelated=body({"i":4},10)
    with subprocess.Popen([str(Path(sys.argv[2]).resolve())],text=True,
                          stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                          stderr=subprocess.DEVNULL) as p:
      def ask(*args):
        p.stdin.write(" ".join(map(str,args))+"\n");p.stdin.flush()
        return p.stdout.readline().strip().split()
      def cmd(ok,*args):
        got=ask(*args)
        assert got==ok,(args,got,ok)
      def one(cap,switched,ready,at,prior,rule):
        cmd(["ok"],"reset",cap)
        cmd(["ok"],"enqueue","Q","Side",diag)
        cmd(["0"] if prior!="received" else ["1","Q:60"],
            "dispatch",0,int(prior!="pending"),int(prior=="received"))
        # The same absence of a callback can have no debit or a live debit.
        cmd(["0"],"dispatch",2,0,1)
        pending=bool(int(ask("pending","Q","Side",diag)[0]))
        spent=int(ask("tx",at,"Q")[0])
        assert pending==(prior=="pending")
        assert spent==60*(prior!="pending" and at<=4)
        receiver="P" if not switched else "Q" if ready else "R"
        remove=False
        if rule=="uniform-fallback" and receiver=="Q" and 173<=cap<233:
            receiver="R"
        if rule=="source-qualified" and receiver=="Q" and cap>=173:
            if spent+173>cap:
                # Need a real earlier authorization for the backup, not
                # retroactive relabelling of the primary sender.
                receiver="R"
            elif pending and spent+60+173>cap:
                cmd(["1"],"remove","Q","Side",diag);remove=True
        cmd(["ok"],"enqueue","Side","Independent",unrelated)
        cmd(["ok"],"enqueue",receiver,"Base",receipt)
        output=ask("dispatch",at,1,1)
        assert "Side:10" in output
        returned=receiver+":173" in output
        assert (receiver,remove,returned)==direct(cap,switched,ready,at,prior,rule)
        return receiver,remove,returned
      stats=[]
      for case in product((172,173,232,233), (False,True),(False,True),(4,5),
                          ("pending","erased","received"),("source-qualified","retained-queue","uniform-fallback")):
        stats.append([*case,*one(*case)])
      assert len(stats)==288
      pair=[r for r in stats if r[:4]==[232,True,True,4] and r[4]!="received"]
      assert [r[-3:] for r in pair]==[["Q",True,True],["Q",False,False],["R",False,True],
                                     ["R",False,True],["Q",False,False],["R",False,True]]
      assert all(r[-1] for r in stats if r[0]>=173 and r[5]=="source-qualified")
      p.stdin.close()
      assert p.wait()==0
    print(json.dumps(dict(native=stats,principal=pair),indent=2,sort_keys=True))

if __name__=="__main__":main()
