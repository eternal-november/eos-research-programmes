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

def trial(root,route,d,q,noise,condition,arm):
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
    offers=root/"offers.db";grant(offers,digest(raw))
    if condition=="Q-stale":
        a=json.loads(cell(victims["Q"]))
        value=a["receipts"][0][3];a["receipts"][0][0]="run:9"
        assert a["receipts"][0][3]==value
        with sqlite3.connect(victims["Q"]) as db:
            db.execute("update seen set effect_cut=? where id=1",(canonical(a),))
    if condition=="Q-missing":victims["Q"].unlink()
    if condition in ("Q-revoked","Q-epoch"):
        with sqlite3.connect(offers) as db:
            db.execute("update ready set "+("active=0" if condition=="Q-revoked" else "epoch=2")+
                       " where peer='Q'")
    w.unlink()
    record=json.loads(raw)
    header=canonical({k:record[k] for k in seal_fields})
    prefix=canonical(omit({k:x for k,x in record.items() if k not in seal_fields}))[offset]
    assert len(header)==114 and prefix=="1"
    if condition=="bad-early":prefix="9"
    send("begin",d,q,noise,encode(header),encode(prefix))
    h,c=map(decode,receive())
    seal=json.loads(h)
    assert h==header and c==prefix
    frame={s:qualify(offers,s,db,seal,c) for s,db in victims.items()}
    if condition=="closed":assert frame["P"]==frame["Q"] is not None
    elif condition=="bad-early":assert not any(frame.values())
    else:assert frame["P"] is not None and frame["Q"] is None
    # Per-supplier reads above are from separate immutable snapshots. The
    # frozen descriptor remains valid through this serial dispatch only.
    send("commit",route,arm,encode(frame["P"]),encode(frame["Q"]))
    if arm:
        tag,*vals=receive()
        assert tag=="cut"
        cut=tuple(map(int,vals))
        assert cut==(int(route!=1),int(route!=0),d+115,q+5,115+noise)
        chosen=select(tuple(s for s,x in frame.items() if x is not None),cut,frame)
        send(chosen)
    selected,who,data,aux,ptx,qtx,rx=receive()
    if arm:assert selected==chosen
    pAvail=frame["P"] is not None and d<=41
    qAvail=frame["Q"] is not None and q<=151
    pGood=pAvail and route!=1 and noise<=41
    qGood=qAvail and route!=0 and noise<=41
    expected=("Q" if qGood else "P" if pGood else "-") if arm else (
              "P" if pGood else "Q" if qGood else "-")
    assert who==expected
    pPaid=(selected=="P") if arm else pAvail
    qPaid=(selected=="Q") if arm else qAvail
    a=int(aux)
    assert a==int(not pPaid)
    assert (int(ptx),int(qtx),int(rx))==(d+115+164*pPaid+4*a,q+5+164*qPaid,
                                            115+noise+164*(who!="-"))
    if data!="-":
        suff=decode(data)
        prepared=suff[:offset]+c+suff[offset:]
        candidate=seal|restore(json.loads(prepared))
        assert canonical(candidate)==raw
        assert ns["direct_adequacy"](dst,basis,candidate)
        assert ns["recovered_prefix"](dst,basis,candidate)
        assert station["install"](dst,candidate["digest"],True)
        assert station["world_has_right"](dst)
        assert ns["restart"](dst)=={"status":"cached","tick":8,"result":[1,0]}
    else:
        with closing(station["open_station"](dst)) as cur:assert station["tag"](cur)==basis
    return [1,int(who!="-"),a,int(who=="Q"),164*(int(pPaid)+int(qPaid)-int(who!="-"))]

def main():
    totals={}
    for route,resources,condition,arm in product(
      (0,1,2),((41,151,0),(40,150,41),(41,151,42),(42,151,0),(41,152,0)),
      ("closed","Q-missing","Q-stale","Q-revoked","Q-epoch","bad-early"),(0,1)):
        if condition!="closed" and resources!=(41,151,0):continue
        with tempfile.TemporaryDirectory() as root:
            got=trial(Path(root),route,*resources,condition,arm)
        name="/".join(map(str,(route,*resources,condition)))
        totals.setdefault(name,[]).append(got)
    service.stdin.close()
    assert service.wait()==0
    print(canonical(totals))
if __name__=="__main__":main()
