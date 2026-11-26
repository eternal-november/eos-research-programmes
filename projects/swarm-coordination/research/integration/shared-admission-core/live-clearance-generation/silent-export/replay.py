"""A frozen donor exits while an independent receiving path may retain its cut."""
from contextlib import closing
from itertools import product
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile

# Load the pinned helpers, not the old program's main or worker dispatch.
path=Path(sys.argv[1])/"prior.py"
scope={}
text=path.read_text()
tail='if len(sys.argv)>2 and sys.argv[2]=="fencer":'
assert text.count(tail)==1
exec(compile(text.split(tail)[0],str(path),"exec"),scope)
key=scope["KEY"]
native=scope["journal"]
open_station=scope["open_station"]
digest=scope["tag"]

def open_witness(path):
    d=sqlite3.connect(path, isolation_level=None)
    assert d.execute("pragma journal_mode=wal").fetchone()==("wal",)
    d.execute("pragma synchronous=full")
    d.execute("create table if not exists seen (id integer primary key, effect_cut text not null)")
    return d

def leave(phase,at):
    if phase==at:os._exit(73)

def closed_packet(donor,checkpoint,kind,token):
    with closing(open_station(donor)) as s:
        top=s.execute("select max(tick) from log").fetchone()[0]
        permit=s.execute("select * from permit order by intent").fetchall()
        logs=s.execute("select * from log where tick>?",(7,)).fetchall()
        receipts=s.execute("select * from receipt where tick>?",(7,)).fetchall()
    if kind=="stopped":
        return {"old_epoch":1,"closed":True}
    if kind=="seal":
        return {"old_epoch":1,"closed":True,"digest":token,"tick":top}
    assert kind=="suffix"
    return {"old_epoch":1,"closed":True,"base":checkpoint,"digest":token,"tick":top,
            "log":logs,"receipts":receipts,"permit":permit}

def exporter(root,phase,kind,checkpoint):
    src=root/"donor.db"
    store=root/"envelope.db"
    leave(phase,"before-fence")
    token=scope["fence"](src)
    leave(phase,"after-fence")
    if kind=="full":
        scope["transfer"](src,root/"frozen.db")
        leave(phase,"after-witness-commit")
        raise AssertionError("fault after copy demand")
    packet=closed_packet(src,checkpoint,kind,token)
    with closing(open_witness(store)) as w:
        w.execute("begin immediate")
        w.execute("insert into seen values(1,?)",(native.encode(packet),))
        leave(phase,"during-witness")
        w.commit()
        leave(phase,"after-witness-commit")
    raise AssertionError("expected silent export")

def recovered_prefix(dst,basis,packet):
    # Temporary transaction: partial/mixed payload cannot alter staged state.
    # No reads of the donor or the true test-side crash point are available.
    if not packet or packet.get("old_epoch")!=1 or packet.get("closed") is not True:
        return False
    if "digest" not in packet:return False
    with closing(open_station(dst)) as d:
        d.execute("begin immediate")
        try:
            if d.execute("select era,can_apply from authority").fetchone()!=(1,1):return False
            if digest(d)!=basis or packet.get("base",basis)!=basis:return False
            if "log" in packet:
                for row in packet["log"]:d.execute("insert into log values(?,?,?)",row)
                for row in packet["receipts"]:d.execute("insert into receipt values(?,?,?,?)",row)
                d.execute("delete from permit")
                for row in packet["permit"]:d.execute("insert into permit values(?,?)",row)
            d.execute("update authority set can_apply=0 where era=1")
            if (digest(d)!=packet["digest"] or
                    d.execute("select max(tick) from log").fetchone()[0]!=packet["tick"]):
                return False
            try:native.reconstruct(d)
            except (AssertionError,ValueError,TypeError):return False
            d.commit()
            return True
        finally:
            if d.in_transaction:d.rollback()

def direct_adequacy(dst,basis,packet):
    # A keyed-prefix null model without replacing the checkpoint. The
    # comparison hashes exactly the same semantic fields in explicit order.
    if not packet or "digest" not in packet:return False
    with closing(open_station(dst)) as d:
        if digest(d)!=basis or packet.get("base",basis)!=basis:return False
        R=list(d.execute("select * from permit order by intent"))
        L=list(d.execute("select * from log order by tick"))
        T=list(d.execute("select * from receipt order by intent"))
    R=packet.get("permit",R)
    L=L+packet.get("log",[])
    T=sorted(T+[tuple(r) for r in packet.get("receipts",[])])
    fields=[[(0,1,0)],R,L,T]
    expected=scope["sha256"](native.encode(fields).encode()).hexdigest()
    return (packet["digest"]==expected and L[-1][0]==packet["tick"]
            and packet.get("old_epoch")==1 and packet.get("closed") is True)

def restart(db):
    # File-independent new worker; uses the ordinary #643 native write cut.
    p=subprocess.run([sys.executable,"-B",str(path),sys.argv[1],"worker",str(db),"2","none"],
                     capture_output=True,text=True)
    assert p.returncode==0,p.stderr
    return json.loads(p.stdout)

def retry_old(db,phase):
    p=subprocess.run([sys.executable,"-B",str(path),sys.argv[1],"worker",str(db),"1",phase],
                     capture_output=True,text=True)
    assert p.returncode==77 and p.stdout=="",(p.stdout,p.stderr)

def receiver(root,basis,auth):
    dst=root/"receiver.db"
    full=root/"frozen.db"
    blob=None
    with closing(open_witness(root/"envelope.db")) as w:
        cell=w.execute("select effect_cut from seen").fetchone()
        if cell:blob=json.loads(cell[0])
    bytes_copy=0
    if full.exists():
        # Separately provisioned comparator: a trusted, completed frozen
        # snapshot is received in the very same scope and move.
        bytes_copy=scope["transfer"](full,dst)
        with closing(open_station(dst)) as d:
            have=d.execute("select era,can_apply from authority").fetchone()
            assert have==(1,0)
            seal=digest(d)
        good=scope["install"](dst,seal,True)
    else:
        direct=direct_adequacy(dst,basis,blob)
        good=recovered_prefix(dst,basis,blob)
        assert good==direct
        if good:
            assert scope["install"](dst,blob["digest"],True)
    if not good:
        with closing(open_station(dst)) as d:
            assert digest(d)==basis # no partial authority/metadata updates
    legal=scope["world_has_right"](dst) if good else False
    entitled=scope["check_start"](good,good,legal,"core")
    if entitled:
        assert auth # evaluator only; current local permit justifies selection
        result=restart(dst)
    else:
        result={"status":"deferred" if not good else "no-permit"}
    return result, 0 if blob is None else len(native.encode(blob)),bytes_copy

def trial(root,old,crash,kind,auth=True,revoke=False):
    src=root/"donor.db"
    dst=root/"receiver.db"
    scope["init"](src,auth)
    stage=scope["transfer"](src,dst)
    with closing(open_station(dst)) as d:basis=digest(d)
    if auth:retry_old(src,old)
    if revoke:
        assert auth and old=="after-stage"
        with closing(open_station(src)) as d:
            assert d.execute("delete from permit where intent=?",(key,)).rowcount==1
    after=scope["state"](src)
    assert (after["has"] is not None)==(auth and old=="after-commit")
    k=subprocess.run([sys.executable,"-B",__file__,sys.argv[1],"export",
                      str(root),crash,kind,basis],capture_output=True,text=True)
    assert k.returncode==73 and k.stdout=="",(k.returncode,k.stdout,k.stderr)
    assert scope["state"](src)["writable"]==int(crash=="before-fence")
    # The receiver is not given that file or handle. After the donor process
    # exits the harness moves its durable DB out of the request's directory.
    hid=root/"offline"
    hid.mkdir()
    for f in root.glob("donor.db*"):f.rename(hid/f.name)
    assert not src.exists()
    a=native.iso.make(native.n,False)
    native.n.step(a,[native.A.NOOP.value,native.A.FORWARD.value])
    assert (a.agents[1].x,a.agents[1].y)==(2,1)
    result,logical,second=receiver(root,basis,auth and not revoke)
    if result["status"] in ("applied","cached"):
        assert result["tick"]==8 and result["result"]==[1,0]
        assert result["status"]==("cached" if old=="after-commit" else "applied")
    return dict(symptom="exporter silent",status=result["status"],trusted_copy=second,
                exported_json=logical,initial_copy=stage,side=1)

def main():
    result={}
    for old,crash,kind in product(("after-stage","after-commit"),
                                 ("before-fence","after-fence","during-witness","after-witness-commit"),
                                 ("stopped","seal","suffix","full")):
        if crash=="during-witness" and kind=="full":continue
        with tempfile.TemporaryDirectory() as d:
            x=trial(Path(d),old,crash,kind)
        expected=crash=="after-witness-commit" and (kind in ("suffix","full") or
                    (kind=="seal" and old=="after-stage"))
        assert expected==(x["status"] in ("applied","cached"))
        result["/".join((old,crash,kind))]=x
    with tempfile.TemporaryDirectory() as d:
        x=trial(Path(d),"after-stage","after-witness-commit","suffix",False)
    assert x["status"]=="no-permit"
    invalid={}
    for kind in ("seal","suffix","full"):
        with tempfile.TemporaryDirectory() as d:
            z=trial(Path(d),"after-stage","after-witness-commit",kind,revoke=True)
        assert z["status"]==("deferred" if kind=="seal" else "no-permit")
        invalid[kind]=z
    print(json.dumps({"cases":result,"empty_authority":x,"revocation_after_checkpoint":invalid},sort_keys=True))

if len(sys.argv)>2:
    assert sys.argv[2]=="export"
    exporter(Path(sys.argv[3]),*sys.argv[4:])
else:
    main()
