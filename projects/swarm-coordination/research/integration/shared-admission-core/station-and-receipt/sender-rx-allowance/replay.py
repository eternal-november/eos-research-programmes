"""Selected sender-policy replay with identical receiver and physical path."""
from itertools import permutations, product
from collections import defaultdict
from pathlib import Path
from random import Random
from hashlib import sha256
import subprocess,json,sys
from joined import body,load_warehouse

def predict(jobs,base,op):
    results=[]
    for i in op:
        n,c=jobs[i]
        if base+n<=c:
            results.append(i)
            base+=n
    return results,base

def main():
    native=load_warehouse().native("buffer",True,True,3,12)
    assert native["settled"] and len(native["native_old"])==1
    packet=[body(dict(ep=91,result=native["native_old"][0]),173),
            body(dict(k="survey"),60)]
    with subprocess.Popen([str(Path(sys.argv[2]).resolve())],text=True,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL) as p:
      def ask(*a):
        p.stdin.write(" ".join(map(str,a))+"\n");p.stdin.flush()
        return p.stdout.readline().strip().split()
      def put(s,d,data):
        assert ask("append",s,d,data)==["ok"]
      def run(ops,cs,base,t,base_cap):
        assert ask("reset",*cs,base_cap)==["ok"]
        if base:
            put("R","Base","61"*base)
            assert ask("run",0)==["1","R:Base"]
        for r in ops:put(("P","Q")[r],"Base",packet[r])
        put("R","Home","62"*10)
        output=ask("run",t)
        matched,expected_rx=predict(list(zip((173,60),cs)),base*(t<=4),ops)
        expected=[("P","Q")[i]+":Base" for i in matched]+["R:Home"]
        assert output==[str(len(expected)),*expected],(ops,cs,base,t,base_cap,output,expected)
        assert int(ask("ledger","Base")[1])==expected_rx
        # All planned TX costs fit in isolation; even an RX rejection
        # leaves the full native sender charge.
        assert ask("ledger","P")==["173","0"]
        assert ask("ledger","Q")==["60","0"]
        return matched
      rows=[]
      for cp,cq,base,t,base_cap,old_first in product(
           (173,200,232,233,263,293),(173,200,232,233,263,293),
           (0,30,60),(4,5),(1,233,900),(False,True)):
        result=run((0,1) if old_first else (1,0),(cp,cq),base,t,base_cap)
        rows.append([cp,cq,base,t,base_cap,old_first,result])
      p.stdin.close();assert p.wait()==0
    # Relationship must survive under the same (opaque) endpoint and
    # opposite role assignments. The single irreversible order choice
    # cannot see which assignment holds if no cap evidence is exposed.
    witness=[row for row in rows if row[:2] in ([200,233],[233,200]) and
             row[2:5]==[0,4,233]]
    assert sorted(len(r[-1]) for r in witness)==[1,1,2,2]
    n=0;robust=0;multicast=0
    R=Random(277)
    for _ in range(520):
        jobs=[(R.randrange(1,10),R.randrange(1,80)) for _ in range(R.randrange(2,7))]
        base=R.randrange(8); ops=tuple(range(len(jobs)))
        feasible=lambda order,j:len(predict(j,base,order)[0])==len(j)
        order=sorted(ops,key=lambda i:jobs[i][1])
        assert feasible(order,jobs)==any(feasible(k,jobs) for k in permutations(ops))
        n+=1
        worlds=[jobs,[(b,max(1,c+R.randrange(-20,21))) for b,c in jobs]]
        mini=[(b,min(w[i][1] for w in worlds)) for i,(b,c) in enumerate(jobs)]
        oo=sorted(ops,key=lambda i:mini[i][1])
        assert feasible(oo,mini)==any(all(feasible(k,w) for w in worlds)
                                    for k in permutations(ops))
        robust+=1
        # Same sender threshold is used at each reached receiver.
        fan=[R.randrange(1,8) for _ in jobs]
        debts=[R.randrange(8) for _ in range(3)]
        def joined(order):
            for d,h in enumerate(debts):
                subset=[i for i in order if fan[i]&(1<<d)]
                if len(predict(jobs,h,subset)[0])!=len(subset):return False
            return True
        assert joined(order)==any(joined(k) for k in permutations(ops))
        multicast+=1
    print(json.dumps(dict(native=len(rows),logical_checks=n,blind_checks=robust,multicast_checks=multicast,
        sha256=sha256(json.dumps(rows).encode()).hexdigest(),witness=witness),
        sort_keys=True,indent=2))

if __name__=="__main__":main()
