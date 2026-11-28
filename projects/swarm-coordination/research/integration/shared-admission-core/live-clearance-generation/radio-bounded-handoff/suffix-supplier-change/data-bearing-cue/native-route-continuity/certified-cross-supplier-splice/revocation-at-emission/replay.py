"""Joined old archive witnesses, received prefix and native pose-driven commit."""
from contextlib import closing
from hashlib import sha256
from itertools import product
from pathlib import Path
import json, sqlite3, subprocess, sys, tempfile

from codec import omit, restore, canonical
from core import Event, Use, Row, admitted
up=Path(sys.argv[1])
ns={}
f=(up/"silent.py").read_text()
anchor='\nif len(sys.argv)>2:\n'
assert f.count(anchor)==1
exec(compile(f.split(anchor)[0],str(up/"silent.py"),"exec"),ns)
station=ns["scope"]
nat=ns["native"]
key=station["KEY"]
codec="suffix-omit-result-95/v1"
offset=95
seal_fields={"old_epoch","closed","digest","tick"}

def readonly(db):
    return sqlite3.connect(db.as_uri()+"?mode=ro",uri=True)
def digest(data):return sha256(data.encode()).hexdigest()
def cell(db):
    if not db.exists():return None
    with closing(readonly(db)) as w:
        result=w.execute("select effect_cut from seen where id=1").fetchone()
    return result[0] if result else None
def snapshot(witness,dst):
    with closing(readonly(witness)) as src, closing(sqlite3.connect(dst)) as out:
        src.backup(out)
        assert out.execute("pragma quick_check").fetchone()==("ok",)
        assert not witness.samefile(dst)
def grant(path,bound):
    with sqlite3.connect(path,isolation_level=None) as g:
        g.execute("create table ready (peer text primary key, key text, epoch int, codec text, digest text, active int)")
        g.executemany("insert into ready values(?,?,?,?,?,1)",
                      [(peer,key,1,codec,bound) for peer in ("P","Q")])

def qualify(offer,who,archive,seal,cue):
    with closing(readonly(offer)) as g:
        row=g.execute("select key,epoch,codec,digest,active from ready where peer=?",(who,)).fetchone()
    if row is None or (row[0],row[1],row[2],row[4])!=(key,seal["old_epoch"],codec,1):
        return None
    data=cell(archive)
    if data is None or digest(data)!=row[3]:return None
    v=json.loads(data)
    if {k:v[k] for k in seal_fields}!=seal:return None
    if not any(r[0]==key and r[2]==seal["tick"] for r in v["receipts"]):return None
    compact=canonical(omit({k:x for k,x in v.items() if k not in seal_fields}))
    assert len(compact)==165
    if compact[offset]!=cue:return None
    return compact[:offset]+compact[offset+1:]

service= subprocess.Popen(sys.argv[2:4],stdin=subprocess.PIPE,stdout=subprocess.PIPE,
                           bufsize=1,text=True)
def send(*terms):
    service.stdin.write(" ".join(map(str,terms))+"\n")
    service.stdin.flush()
def receive():
    return service.stdout.readline().split()
def encode(x):return "-" if x is None else x.encode().hex()
def decode(x):return None if x=="-" else bytes.fromhex(x).decode()

def select(offer,cut,frame):
    # Binding and route facts are earned from separate local interfaces.
    # Compress the live meter into one same-cut prior debit per resource;
    # here there is one serial dispatch, so no future expiry is queried.
    p,q,np,nq,rx=cut
    facts=frozenset(s for s,r in (("P",p),("Q",q)) if r and frame[s] is not None)
    past=tuple(Event(8,i,uses=(Use((k,),n,320,4),))
               for i,(k,n) in enumerate(zip(("P","Q","Base"),(np,nq,rx))))
    aux=Event(8,5,uses=(Use(("P",),4,320,4),),paid=("aux",))
    def old(s):
        n=164 if frame[s] is None else len(frame[s])
        return Event(8,4,need=frozenset((s,)),uses=(Use((s,),n,320,4),Use(("Base",),n,320,4)),
                     paid=("old",))
    proposals={s:(old(s),aux) for s in ("P","Q")}
    r=Row(((8,"local",offer),),facts,past,proposals)
    both=next(iter(admitted([r],"local",8,{"old":8,"aux":8},("P","Q")).values()))
    if both:actual=both[0]
    else:
        possible={s:(old(s),) for s in ("P","Q")}
        rr=Row(r.receipts,r.facts,r.events,possible)
        single=next(iter(admitted([rr],"local",8,{"old":8},("P","Q")).values()))
        actual=single[0] if single else "-"
    # Strongest same-cut arithmetic including allocation of the aux work.
    pOk="P" in facts and np+164<=320 and rx+164<=320
    qOk="Q" in facts and nq+164<=320 and rx+164<=320
    direct="Q" if qOk else "P" if pOk else "-"
    assert actual==direct
    return actual


def mutate(path,sql):
    with closing(sqlite3.connect(path,timeout=0,isolation_level=None)) as w:
        try:w.execute(sql)
        except sqlite3.OperationalError as e:
            assert e.sqlite_errorcode in (sqlite3.SQLITE_BUSY,sqlite3.SQLITE_LOCKED)
            return False
        return True

def ack(path):
    with closing(readonly(path)) as g:
        return not g.execute("select active from ready where peer='Q'").fetchone()[0]

def trial(root,route,layout,timing,policy):
    d,q,noise=41,151,0
    src,dst,w=(root/x for x in ("donor.db","receiver.db","envelope.db"))
    station["init"](src,True)
    assert station["transfer"](src,dst)==32768
    with closing(station["open_station"](dst)) as cur:basis=station["tag"](cur)
    ns["retry_old"](src,"after-commit")
    worker=subprocess.run([sys.executable,"-B",str(up/"silent.py"),str(up),"export",
                           str(root),"after-witness-commit","suffix",basis],
                          capture_output=True,text=True)
    assert worker.returncode==73 and not worker.stdout,worker.stderr
    donor=root/"donor-offline";donor.mkdir()
    for f in root.glob("donor.db*"):f.rename(donor/f.name)
    assert not src.exists()
    victims={s:root/(s+".db") for s in ("P","Q")}
    for db in victims.values():snapshot(w,db)
    assert victims["P"].stat().st_ino!=victims["Q"].stat().st_ino
    # The original writer and one shared witness are not consulted at the
    # cut. No claim these are distinct physical failure domains.
    raw=cell(victims["P"])
    assert raw==cell(victims["Q"])
    dbs={s:root/(s+"-offers.db" if layout=="scoped" else "offers.db") for s in ("P","Q")}
    for db in set(dbs.values()):
        grant(db,digest(raw))
        with sqlite3.connect(db) as g:g.execute("create table independent_work (v int)")
    Q=dbs["Q"];P=dbs["P"]
    if layout=="scoped":
        for own,path in dbs.items():
            with sqlite3.connect(path) as g:
                g.execute("delete from ready where peer<>?",(own,))
                assert g.execute("select peer from ready").fetchall()==[(own,)]

    w.unlink()
    record=json.loads(raw)
    header=canonical({k:record[k] for k in seal_fields})
    prefix=canonical(omit({k:x for k,x in record.items() if k not in seal_fields}))[offset]
    send("begin",d,q,noise,encode(header),encode(prefix))
    h,c=map(decode,receive())
    assert (h,c)==(header,prefix)
    seal=json.loads(h)
    def inspect():
        return {s:qualify(dbs[s],s,db,seal,c) for s,db in victims.items()}
    pre=inspect()
    assert pre["P"]==pre["Q"] is not None
    send("commit",route,1,encode(pre["P"]),encode(pre["Q"]))
    tag,*vs=receive()
    live=tuple(map(int,vs))
    assert tag=="cut" and live==(int(route!=1),1,156,156,115)
    revoke=lambda:mutate(Q,"update ready set active=0 where peer='Q'")
    independent=lambda:mutate(P,"insert into independent_work values(1)")
    revoked=None;holder=None
    if timing=="before":revoked=revoke();assert revoked
    if policy=="locked" and timing=="gap":
        holder=sqlite3.connect(Q,timeout=0,isolation_level=None)
        holder.execute("begin immediate")
        assert holder.execute("select active from ready where peer='Q'").fetchone()==(1,)
    state=pre if policy=="cached" else inspect()
    chosen=select(tuple(s for s,x in state.items() if x is not None),live,state)
    if timing=="gap":revoked=revoke()
    independent_in_cut=independent()
    assert ack(Q)==revoked
    send(chosen)
    selected,who,data,aux,ptx,qtx,rx=receive()
    assert who==selected==chosen
    unauthorized=who=="Q" and ack(Q)
    if holder:
        assert holder.in_transaction
        holder.commit()
        holder.close()
        assert revoked is False and revoke()
    assert ack(Q)
    if not independent_in_cut:assert independent()
    with closing(readonly(P)) as g:
        assert g.execute("select count(*) from independent_work").fetchone()==(1,)
    if data!="-" and not unauthorized:
        suff=decode(data)
        prepared=suff[:offset]+c+suff[offset:]
        candidate=seal|restore(json.loads(prepared))
        assert canonical(candidate)==raw
        assert ns["direct_adequacy"](dst,basis,candidate)
        assert ns["recovered_prefix"](dst,basis,candidate)
        assert station["install"](dst,candidate["digest"],True)
        assert ns["restart"](dst)=={"status":"cached","tick":8,"result":[1,0]}
        settled=True
    else:
        settled=False
        with closing(station["open_station"](dst)) as cur:assert station["tag"](cur)==basis
    hold=policy=="locked" and timing=="gap"
    assert revoked== (not hold)
    assert independent_in_cut==(not hold or layout=="scoped")
    assert unauthorized==(policy=="cached" or policy=="refresh" and timing=="gap")
    assert settled==(hold or (not unauthorized and route==2))
    assert int(ptx)==156+164*int(who=="P")+4*int(aux)
    assert int(qtx)==156+164*int(who=="Q")
    assert int(rx)==115+164*int(who!="-")
    return dict(selected=chosen,revocation_committed_by_effect=revoked,
                unauthorized_delivery=unauthorized,exact_return=settled,
                independent_write_at_cut=independent_in_cut,aux=bool(int(aux)))

def main():
    totals={}
    for route,layout,timing,policy in product((1,2),("shared","scoped"),("before","gap"),
                                              ("cached","refresh","locked")):
        with tempfile.TemporaryDirectory() as root:
            got=trial(Path(root),route,layout,timing,policy)
        totals["/".join(map(str,(route,layout,timing,policy)))]=got
    service.stdin.close()
    assert service.wait()==0
    print(canonical(totals))
if __name__=="__main__":main()
