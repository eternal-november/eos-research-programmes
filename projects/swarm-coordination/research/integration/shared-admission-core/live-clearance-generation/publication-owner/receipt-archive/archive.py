"""Two actual selected producers; one post-closure decision routine."""
from pathlib import Path
import hashlib
import json
import sqlite3
import subprocess
import sys
import tempfile

root=Path(__file__).resolve().parent
# The original loader's public worker mode stays untouched. Only its CLI
# dispatch is omitted inside this driver; worker subprocesses run that file.
p=root/"warehouse_replay.py"
data=p.read_bytes()
assert hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()=="13356cc4054027020aeb4b2f204e3d738286cbe4"
ns={"__file__":str(p),"__name__":"warehouse_fixture"}
sys.argv=[str(p),str(root)]
src=data.decode()
exec(compile(src[:src.index('if len(sys.argv)>2 and sys.argv[2]=="fencer"')],str(p),"exec"),ns)
native=ns["journal"]
artifact_key="inspection_100.000002_100.000000_100.000000"

def archive(db,evidence):
    with sqlite3.connect(db) as d:
        d.execute("create table witness (payload text not null)")
        if evidence is not None:
            d.execute("insert into witness values (?)",(json.dumps(evidence),))

def decide(db,source,key,epoch):
    # Called AFTER the control event that closes the old lookup.
    with sqlite3.connect(db) as d:
        row=d.execute("select payload from witness").fetchone()
    if row is None:return "refuse"
    w=json.loads(row[0])
    if (w["plant"],w["key"],w["epoch"],w["at"])!=(source,key,epoch,1):
        return "refuse"
    if w["result"] is not None:return "return"
    if w["fence"] and w["permit"]:return "apply"
    return "refuse"

def scorer(home,kind):
    p=subprocess.Popen([str(root/"score"),"exact" if kind not in ("alias","late") else "sibling",
                        "late" if kind=="late" else "none"],
                       stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    pre=json.loads(p.stdout.readline())
    assert pre["key"]==artifact_key and pre["epoch"]==7 and pre["at"]==1
    row={"plant":"score","key":pre["key"],"epoch":pre["epoch"],"at":pre["at"],
         "result":pre["delta"] if pre["present"] else None,"fence":False,"permit":False}
    if kind=="stale":row["epoch"]-=1
    db=home/"archive.db";archive(db,None if kind=="lost" else row)
    # The exporter acknowledged the archive write, not final scout read.
    post,_=p.communicate("next\n",timeout=10)
    assert p.returncode==0
    close=json.loads(post)
    assert close["other_delta"]==1 and close["closed_status"]=="scoring finished"
    evident=decide(db,"score",artifact_key,7)
    assert evident==("return" if kind=="qualified" else "refuse")
    if kind=="late":assert not pre["present"] and close["end_present"]==1
    if kind=="alias":assert close["end_present"]==0
    return {"decision":evident,"other":close["other_delta"],"old_source":close["closed_status"]}

def warehouse(home,kind):
    src=home/"old.db"; dst=home/"new.db"
    allowed=(kind!="denied")
    ns["init"](src,allowed)
    old_committed=kind in ("old-first","old-first-copy","stale")
    if old_committed:
        assert ns["run"](src,1)["status"]=="applied"
    receipt=ns["fence"](src)
    # A confirmed old result can be exported from the fenced owner without
    # handing over the ability to change the warehouse at all.
    captured=ns["state"](src)["has"]
    copied=0
    if not captured or kind=="old-first-copy":
        copied=ns["transfer"](src,dst)
        assert ns["install"](dst,receipt,True)
        assert ns["state"](dst)["has"]==captured
    row={"plant":"warehouse","key":ns["KEY"],"epoch":7,"at":1,
         "result":json.loads(captured[0]) if captured else None,"fence":True,
         "permit":bool(copied) and ns["world_has_right"](dst)}
    if kind=="stale": row["at"]=0
    if kind=="unfenced-cut":row["fence"]=False
    db=home/"archive.db";archive(db,row)
    # An actual independent native movement. The application handoff at this
    # cut removes the successor's old-source read capability by construction.
    side=native.iso.make(native.n,False)
    actor=side.agents[1];native.n.step(side,[ns["A"].NOOP.value,ns["A"].FORWARD.value])
    assert (actor.x,actor.y)==(2,1)
    decision=decide(db,"warehouse",ns["KEY"],7)
    request=ns["run"](dst,2) if decision=="apply" else None
    old=ns["run"](src,1);assert old["status"]=="refused"
    if kind in ("old-first","old-first-copy"):
        assert decision=="return" and row["result"]==[1,0] and ns["state"](src)["tick"]==8
        assert (not copied)==(kind=="old-first")
        if copied:assert ns["state"](dst)["tick"]==8
    elif kind=="fence-first":
        assert decision=="apply" and request["status"]=="applied" and request["tick"]==8
    else:
        assert decision=="refuse"
    return {"decision":decision,"other":[2,1],"old_source":old["status"],
            "performed":request["status"] if request else None,"copied_snapshot_bytes":copied}

def main():
    results={}
    for name,run,arms in [
        ("score",scorer,["qualified","stale","alias","late","lost"]),
        ("warehouse",warehouse,["old-first","old-first-copy","fence-first","stale","denied","unfenced-cut"])
    ]:
        for arm in arms:
            with tempfile.TemporaryDirectory() as h: results[name+"/"+arm]=run(Path(h),arm)
    print(json.dumps(results,sort_keys=True))
if __name__=="__main__":main()
