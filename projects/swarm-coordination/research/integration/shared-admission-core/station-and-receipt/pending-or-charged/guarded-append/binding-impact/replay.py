"""Civil simulator test: normal receive binding changes after two commitments."""
from itertools import product
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
from joined import body,load_warehouse

def main():
    native=load_warehouse().native("buffer",True,True,3,12)
    assert native["settled"] and len(native["native_old"])==1
    event=native["native_old"][0]
    payloads={"Base":body(dict(ep=5,result=event),173),
              "Home":body(dict(ep=6,result=event),173),
              "Side":body(dict(k="optional"),60),
              "Independent":body({"i":4},10)}
    with subprocess.Popen([str(Path(sys.argv[2]).resolve())],text=True,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL) as proc:
      def ask(*a):
        proc.stdin.write(" ".join(map(str,a))+"\n");proc.stdin.flush()
        return proc.stdout.readline().strip().split()
      def put(s,d):
        assert ask("enqueue",s,d,payloads[d])==["ok"]
      def both(q,p,capQ,capP,target,arm):
        assert ask("reset",400,capQ,capP)==["ok"]
        if q:put("Q","Side")
        if p:put("P","Side")
        put("Q","Base");put("P","Home")
        if not q:put("Q","Side")
        if not p:put("P","Side")
        put("R","Independent")
        assert ask("dispatch",0,0,1)==["0"]  # initial ready-to-append batch is pending
        accepted,visits=map(int,ask("bind",target+":7",arm,capQ,capP))
        assert visits==(0 if arm=="stock" else 5)
        demandQ=173+60*q*(1+(target=="Side"))
        demandP=173+60*p*(1+(target=="Side"))
        assert bool(accepted)==(arm=="stock" or
              capQ>=demandQ and (arm=="one-sender" or capP>=demandP))
        native=ask("dispatch",2,1,1)
        got=["Q:173" in native,"P:173" in native]
        expected=[capQ>=(demandQ if accepted else 173+60*q),
                  capP>=(demandP if accepted else 173+60*p)]
        assert got==expected,(q,p,capQ,capP,target,arm,native,expected)
        assert "R:10" in native
        return [bool(accepted),*got]
      rows=[]
      for q,p,cq,cp,target,arm in product((0,1),(0,1),(173,232,233,292,293),
                  (173,232,233,292,293),("Side","Base","Independent"),
                  ("stock","one-sender","joint")):
        if cq>=173+60*q and cp>=173+60*p:
          rows.append([q,p,cq,cp,target,arm,*both(q,p,cq,cp,target,arm)])
      blocked={}
      for arm in ("stock","one-sender","joint"):
          ss=[r for r in rows if r[5]==arm]
          blocked[arm]=[len(ss),sum(not r[6] for r in ss),sum(not all(r[7:]) for r in ss)]
      assert blocked["joint"][-1]==0 and blocked["one-sender"][-1]>0
      # Membership, not enough sender headroom, is the relevant premise.
      assert ask("reset",400,293,293)==["ok"]
      put("Q","Base");put("P","Home")
      assert ask("unregister","Base")==["1"]
      departed=ask("dispatch",2,1,1)
      assert departed==["1","P:173"]
      proc.stdin.close(); assert proc.wait()==0
    examples=[r for r in rows if r[:5] in ([1,1,293,233,"Side"],[1,1,293,293,"Side"],
                                         [1,1,233,233,"Base"],[0,0,173,173,"Side"])]
    print(json.dumps(dict(rows=len(rows),hash=sha256(json.dumps(rows).encode()).hexdigest(),
          summary=blocked,examples=examples,membership_control=departed),sort_keys=True,indent=2))
if __name__=="__main__":main()
