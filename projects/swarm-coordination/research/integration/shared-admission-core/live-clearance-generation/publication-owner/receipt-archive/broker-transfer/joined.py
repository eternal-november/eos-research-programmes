"""One live ordered history, not a join of prerecorded successes."""
from collections import Counter
from itertools import product
from pathlib import Path
import subprocess
import sqlite3
import tempfile
import json

root=Path(__file__).resolve().parent
KEY="inspection_100.000002_100.000000_100.000000"

def read_archive(path,pre):
    with sqlite3.connect(path) as d:
        d.execute("create table result (key text, epoch integer, at integer, result integer)")
        if pre["present"]:d.execute("insert into result values (?,?,?,?)",
                           (pre["key"],pre["epoch"],pre["at"],pre["delta"]))
    with sqlite3.connect(path) as d:
        found=d.execute("select result from result where key=? and epoch=7 and at=1",(KEY,)).fetchone()
    return found is not None and found[0]==1

def execute(path,source,copy,fail,erase,mode,notice,workload):
    with subprocess.Popen([str(root/"score"),source,"none"],stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE,text=True) as scorer:
      pre=json.loads(scorer.stdout.readline())
      actual=read_archive(path,pre)
      with subprocess.Popen([str(root/"bridge"),"copy" if copy else "none",
              "fail" if fail else "continue","erase" if erase else "clean",mode,
              "loud" if notice else "mute",workload],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as radio:
        radio.stdin.write("A1\n" if actual else "none\n");radio.stdin.flush()
        staged=json.loads(radio.stdout.readline())
        # Native side scoring and closure are actually invoked on this
        # continuing source process after real staging callbacks.
        output,_=scorer.communicate("next\n",timeout=5)
        closed=json.loads(output);assert scorer.returncode==0
        assert closed["other_delta"]==1 and closed["closed_status"]=="scoring finished"
        raw,_=radio.communicate("closed\n",timeout=5)
        done=json.loads(raw);assert radio.returncode==0
    return actual,staged,closed,done

def check(out,source,copy,fail,erase,mode,notice,workload):
    # Independent direct inequalities on the same effects and readiness.
    actual,staged,closed,done=out
    approved=source=="exact"
    assert actual==approved
    assert staged=={"P":int(approved),"Q":int(approved and copy and not erase),
                    "stage_bytes":int(approved)*(2+2*copy)}
    assert closed["end_present"]==int(approved)
    target_exists=approved and (not fail or (copy and not erase))
    slot=9 if mode=="wait" else 5
    old=0 if slot>8 else 3
    size=2 if mode in ("short","stale") else 3
    sent_debit=4 if fail and workload=="late" and slot<=7 else 0
    arrival=notice and target_exists and old+size<=5 and sent_debit+size<=5
    declared=slot if arrival and mode!="stale" else -1
    assert done["raw"]==arrival and done["receipt"]==declared and done["other"]==1
    assert done["older"]==(workload!="off")
    assert done["egress"]==(declared+3 if declared>=0 else 9)

def main():
    counts=Counter();cases={}
    for source,copy,fail,erase,mode,notice,workload in product(
        ("exact","sibling"),(False,True),(False,True),(False,True),
        ("short","full","wait","stale"),(False,True),("off","early","late")):
        with tempfile.TemporaryDirectory() as d:
            out=execute(Path(d)/"a.db",source,copy,fail,erase,mode,notice,workload)
        check(out,source,copy,fail,erase,mode,notice,workload)
        _,stage,closed,done=out
        counts.update(cases=1,on_time=int(done["egress"]<=8),independent=done["other"],
                      independent_score=closed["other_delta"])
        if source=="exact" and fail and notice:
            label=None
            if copy and not erase:label=mode
            if mode=="short" and copy and erase:label="erased-copy"
            if mode=="short" and not copy and not erase:label="primary-only"
            if label and (workload=="off" or label=="short"):
                cases[label if workload=="off" else workload+"-old-work"]=dict(stage=stage,done=done)
    print(json.dumps({"sweep":counts,"after_primary_loss":cases},sort_keys=True))
if __name__=="__main__":main()
