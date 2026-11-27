"""Native static ceilings vs an exact, same-window pre-enqueue guard."""
from pathlib import Path
from itertools import product
import json, subprocess
from replay import inputs

P=Path(__file__).parent
def compare(seed,pc,qc,bc,order,q_up,timeline,x,guard):
    cs={"P":pc,"Q":qc,"R":bc}
    tx={k:0 for k in cs}
    rx=x
    a=b=c=fenced=0
    p_up=order=="ba"
    for evt in timeline:
        actor="R" if evt=="B" else "P" if evt=="C" else evt
        n=10 if evt=="B" else 9
        if evt in "PQ" and guard and a:
            fenced+=1
            continue
        if tx[actor]+n>cs[actor]:
            continue
        tx[actor]+=n
        source_up=p_up if actor=="P" else q_up if actor=="Q" else True
        if not source_up or rx+n>cs[actor]:
            continue
        rx+=n
        if evt=="B":b+=1
        elif evt=="C":c+=1
        else:a+=1
    expected=(a,b,c,fenced,tx["P"],tx["Q"],rx,1)
    raw=subprocess.run([str(P/"static_ceilings"),str(pc),str(qc),str(bc),order,
            str(int(q_up)),timeline,str(x),str(int(guard)),"sealed-fixture"],
            input=seed,check=True,text=True,capture_output=True).stdout
    got=tuple(map(int,raw.split()))
    args=(pc,qc,bc,order,q_up,timeline,x,guard)
    assert got==expected,(args,got,expected)
    return got
def ok(v,distinct=False):
    return v[0]>=1 and v[1]==1 and (not distinct or v[2]==1)
def main():
    graph,xyz,d=inputs()
    ids=(3,2,39)
    pts=(xyz[3],xyz[39],(49,50,0),(51,50,0))
    seed="1\n"+" ".join(map(str,(*ids,*(d[i][j] for i in ids for j in ids),
                              *(n for p in pts for n in p),25.51)))+"\n"
    results={}; checks=0
    for limbs in product((17,18,19,27,28),(17,18,19),(0,8,9),("ab","ba"),
                          (False,True),("PQB","QPB","BPQ","BQP","QPBC"),(False,True)):
        pc,qc,x,order,q_up,tl,g=limbs
        bc=x+19
        got=compare(seed,pc,qc,bc,order,q_up,tl,x,g)
        checks+=1
        if pc>=x+9 and qc>=x+9 and tl in ("PQB","QPB") and (order=="ba" or q_up):
            if g or (pc<x+18 and qc<x+18):
                assert ok(got) and got[0]==1,(limbs,got)
        if x==0 and (pc,qc) in ((17,17),(19,19),(28,19)):
            results["/".join(map(str,limbs))]=got
    def check(p,q,r,order,avail,tl,g=False):
        return compare(seed,p,q,r,order,avail,tl,0,g)
    # Exhaust both fixed sender caps at the held receiver budget. All
    # three histories are required: dual A-first, either sole A after B.
    mixed=[("ba",True,"PQB"),("ba",False,"BPQ"),("ab",True,"BQP")]
    ceiling_pass=0
    for pc,qc in product(range(33),repeat=2):
        rows=[check(pc,qc,19,o,qu,tl) for o,qu,tl in mixed]
        checks+=len(rows)
        ceiling_pass+=int(all(map(ok,rows)))
    assert ceiling_pass==0
    mixed_guard=[check(19,19,19,o,qu,tl,True) for o,qu,tl in mixed]
    checks+=len(mixed_guard)
    assert all(map(ok,mixed_guard))
    # Holding fixed R=19: C shares P's static cap, follows B, and is
    # physically viable (same P path). Setting R=28 is a distinct budget.
    cps=[check(28,19,19,"ba",True,"QPBC",g) for g in (False,True)]
    checks+=len(cps)
    assert not ok(cps[0],True) and ok(cps[1],True)
    quiet=[check(17,17,19,o,qu,tl) for o,qu in (("ba",False),("ab",True),("ba",True))
               for tl in ("PQB","QPB")]
    checks+=len(quiet)
    assert all(map(ok,quiet))
    print(json.dumps({"trials":checks,"quiet":quiet,"mixed_static_passing":ceiling_pass,
            "mixed_guard":mixed_guard,"distinct":cps,"controls":results},sort_keys=True))
if __name__=="__main__":main()
