"""R2 development: two overlapping keyed retries and two source publication transfers."""
from contextlib import closing
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import sqlite3
import subprocess
import sys
import tempfile
from trace_queries import source

AKEY=source.KEY
COMMANDS={AKEY:source.PAYLOAD,"run:next":source.plan[source.i+1]}
BKEY="run:next"
enc=source.journal.encode

TABLES={"authority":"scope","permit":"intent","receipt":"intent","log":None}
def install(conn):
    conn.executescript("""
    CREATE TABLE generation(
      scope TEXT, atom TEXT, rev INTEGER NOT NULL CHECK(typeof(rev)='integer' AND rev>=1),
      PRIMARY KEY(scope,atom)
    ) WITHOUT ROWID;
    """)
    for t,k in TABLES.items():
        for event,rows in (("insert",("new",)),("delete",("old",)),("update",("old","new") if k else ("new",))):
            commands=[]
            for r in rows:
                key=f"cast({r}.{k} as text)" if k else "'*'"
                if event=="update" and r=="new" and k:
                    query=f"SELECT '{t}',{key},1 WHERE old.{k}<>new.{k}"
                else:query=f"VALUES('{t}',{key},1)"
                commands.append(f"INSERT INTO generation {query} ON CONFLICT(scope,atom) DO UPDATE SET rev=rev+1;")
            conn.executescript(f"CREATE TRIGGER journal_{t}_{event} AFTER {event} ON {t} BEGIN {' '.join(commands)} END;")
def v(conn,t,k):
    row=conn.execute("SELECT rev FROM generation WHERE scope=? AND atom=?",(t,k)).fetchone()
    return row[0] if row else 0

def view(conn,key,era):
    a=conn.execute("select era,can_apply from authority where scope=0").fetchone()
    p=conn.execute("select payload from permit where intent=?",(key,)).fetchone()
    slices={("authority","0"):a,("permit",key):p}
    if a!=(era,1) or p!=(enc(COMMANDS[key]),):
        return "refused",slices
    r=conn.execute("select tick,result from receipt where intent=?",(key,)).fetchone()
    slices["receipt",key]=r
    if r is not None:
        return "cached",slices
    rows=tuple(conn.execute("select tick,payload,result from log order by tick"))
    slices["log","*"]=rows
    return "pending",slices

def read(c,key,era):
    meta=c.execute("select id from source_identity").fetchone()[0]
    mode,data=view(c,key,era)
    return (meta,mode,data,{k:v(c,*k) for k in data},(key,era))

def validate(c,old,key,era):
    c.execute("begin")
    tag=c.execute("select id from source_identity").fetchone()[0]
    reads=1
    okay=tag==old[0] and (key,era)==old[4]
    if okay:
        for k,rev in old[3].items():
            reads+=1
            if v(c,*k)!=rev:
                okay=False
                break
    # Guarded path returns the old projection only at this common read cut.
    served=old if okay else read(c,key,era)
    # Audit oracle; not charged as a lookup on the candidate's guarded path.
    fresh=read(c,key,era)
    assert served==fresh,(served,fresh)
    c.rollback()
    return okay,served,reads

def snap(db,key,era):
    with closing(source.open_station(db)) as c:
        c.execute("begin")
        ans=read(c,key,era)
        c.rollback()
        return ans

def age(db,old,key,era):
    with closing(source.open_station(db)) as c:
        return validate(c,old,key,era)

def op(db,key,era,phase="none"):
    # Actual baseline worker's function body with specified named intent and native command.
    source.KEY,source.PAYLOAD=key,COMMANDS[key]
    return source.authorized_step(db,era,phase)

def run(db,key,era,phase):
    p=subprocess.run([sys.executable,"-B",__file__,sys.argv[1],"worker",str(db),key,str(era),phase],
                     text=True,capture_output=True)
    assert p.returncode==77 and not p.stdout,p
def origin(db,noise,watch=True):
    source.KEY,source.PAYLOAD=AKEY,COMMANDS[AKEY]
    source.init(db,True)
    with closing(source.open_station(db)) as c:
        c.execute("insert into permit values (?,?)",(BKEY,enc(COMMANDS[BKEY])))
        for k in range(noise):
            no=source.A.NOOP.value
            source.journal.apply(c,f"warm:{k}",(no,no),"none","bundled")
        if watch:
            install(c)
            c.executescript("create table source_identity(id text not null); insert into source_identity values('station-one');")

def seal_sidecar(c):
    return sha256(enc([list(c.execute("select * from source_identity")),
                       list(c.execute("select * from generation order by scope,atom"))]).encode()).hexdigest()

def freeze(db,old_era):
    with closing(source.open_station(db)) as c:
        c.execute("begin immediate")
        # The #643 one-way fence SQL generalized only in the era parameter.
        n=c.execute("update authority set can_apply=0 where scope=0 and era=? and can_apply=1",(old_era,)).rowcount
        assert n==1
        cut=(source.tag(c),seal_sidecar(c),old_era)
        c.commit()
        return cut

def activate(db,cut,new_id,sidecar=True):
    if cut is None:return False
    seal,index_digest,era=cut
    with closing(source.open_station(db)) as c:
        c.execute("begin immediate")
        a=c.execute("select era,can_apply from authority where scope=0").fetchone()
        if a!=(era,0) or source.tag(c)!=seal or (sidecar and seal_sidecar(c)!=index_digest):
            c.rollback()
            return False
        c.execute("update authority set era=?,can_apply=1 where scope=0",(era+1,))
        c.execute("update source_identity set id=?",(new_id,))
        c.commit()
        return True

def sidecar_bytes(c):
    return len(enc(list(c.execute("select * from generation order by scope,atom"))).encode())

def exercise(root,fa,fb,late,noise,tamper):
    d0,d1,d2=(root/f"{i}.db" for i in range(3))
    origin(d0,noise)
    a0,b0=(snap(d0,k,1) for k in (AKEY,BKEY))
    assert a0[1]==b0[1]=="pending"
    run(d0,AKEY,1,fa)
    a_keep,a_after,_=age(d0,a0,AKEY,1)
    b_keep,b_after,_=age(d0,b0,BKEY,1)
    assert a_keep==b_keep==(fa=="after-stage")
    assert a_after[1]==("pending" if a_keep else "cached")
    assert b_after[1]=="pending"
    cut1=freeze(d0,1)
    bytes1=source.transfer(d0,d1)
    assert activate(d1,cut1,"station-two")
    assert op(d0,AKEY,1)["status"]=="refused"
    a1=op(d1,AKEY,2)
    assert a1["status"]==("applied" if a_keep else "cached")
    ca1,cb1=(snap(d1,k,2) for k in (AKEY,BKEY))
    assert (ca1[1],cb1[1])==("cached","pending")
    assert ("log","*") not in ca1[3] and ("log","*") in cb1[3]
    run(d1,BKEY,2,fb)
    a_stable,fa1,a_reads=age(d1,ca1,AKEY,2)
    b_stable,fb1,b_reads=age(d1,cb1,BKEY,2)
    assert a_stable and b_stable==(fb=="after-stage")
    cut2=freeze(d1,2)
    bytes2=source.transfer(d1,d2)
    # Make a side move on an independent native domain while only dependent work waits.
    side=source.journal.iso.make(source.journal.n,False)
    a=side.agents[1]
    source.journal.n.step(side,[source.A.NOOP.value,source.A.FORWARD.value])
    assert (a.x,a.y)==(2,1)
    ans=op(d2,BKEY,3) if activate(d2,None if late else cut2,"station-three") else {"status":"wait"}
    if late:
        assert ans["status"]=="wait"
        assert op(d2,BKEY,3)["status"]=="refused"
        assert activate(d2,cut2,"station-three")
        ans=op(d2,BKEY,3)
    assert ans["status"]==("applied" if b_stable else "cached")
    assert op(d1,BKEY,2)["status"]=="refused"
    assert op(d2,AKEY,3)["status"]=="cached"
    assert not age(d2,ca1,AKEY,3)[0]
    with closing(source.open_station(d2)) as c:
        g=source.journal.reconstruct(c)
        assert g._cur_steps==source.i+noise+2
        assert c.execute("select count(*) from receipt where intent in (?,?)",(AKEY,BKEY)).fetchone()==(2,)
        meta=sidecar_bytes(c)
    if tamper:
        # Same native snapshot, but changing a generation after the fence
        # cannot transport a retained dependency certificate.
        alt=root/"sidecar.db"
        source.transfer(d1,alt)
        with closing(source.open_station(alt)) as c:
            c.execute("update generation set rev=rev+1 where scope='authority' and atom='0'")
        assert not activate(alt,cut2,"wrong-port")
        # Original whole-native direct handoff ignores generation because it rereads source.
        assert activate(alt,cut2,"direct-control",sidecar=False)
    return [a1["status"],ans["status"],a_stable,b_stable,bytes1+bytes2,meta,
            len(cb1[2]["log","*"]),int(late),a_reads,b_reads]

def direct(root,fa,fb,late,noise):
    # Uninstrumented exact reference: permit, cached receipt, native log path and whole-source seal.
    d0,d1,d2=(root/f"{i}.db" for i in range(3))
    origin(d0,noise,watch=False)
    def ref(db,key,era):
        with closing(source.open_station(db)) as c:
            c.execute("begin")
            m,x=view(c,key,era)
            c.rollback()
            return m,x
    def transfer(src,dst,era,delay):
        if era==1:
            tag=source.fence(src)
        else:
            with closing(source.open_station(src)) as c:
                c.execute("begin immediate")
                assert c.execute("update authority set can_apply=0 where scope=0 and era=2 and can_apply=1").rowcount==1
                tag=source.tag(c)
                c.commit()
        size=source.transfer(src,dst)
        if delay:
            assert op(dst,BKEY,era+1)["status"]=="refused"
        if era==1:
            assert source.install(dst,tag,True)
        else:
            with closing(source.open_station(dst)) as c:
                c.execute("begin immediate")
                assert c.execute("select era,can_apply from authority where scope=0").fetchone()==(2,0)
                assert source.tag(c)==tag
                c.execute("update authority set era=3,can_apply=1 where scope=0")
                c.commit()
        return size
    run(d0,AKEY,1,fa)
    size=transfer(d0,d1,1,False)
    assert op(d0,AKEY,1)["status"]=="refused"
    a1=op(d1,AKEY,2)
    xa,xb=(ref(d1,k,2) for k in (AKEY,BKEY))
    run(d1,BKEY,2,fb)
    a_stable,b_stable=(ref(d1,k,2)==base for k,base in ((AKEY,xa),(BKEY,xb)))
    size+=transfer(d1,d2,2,late)
    b1=op(d2,BKEY,3)
    assert op(d1,BKEY,2)["status"]=="refused" and op(d2,AKEY,3)["status"]=="cached"
    side=source.journal.iso.make(source.journal.n,False)
    actor=side.agents[1]
    source.journal.n.step(side,[source.A.NOOP.value,source.A.FORWARD.value])
    assert (actor.x,actor.y)==(2,1)
    with closing(source.open_station(d2)) as c:
        g=source.journal.reconstruct(c)
        assert g._cur_steps==source.i+noise+2
        assert c.execute("select count(*) from receipt where intent in (?,?)",(AKEY,BKEY)).fetchone()==(2,)
    return [a1["status"],b1["status"],a_stable,b_stable,size]

def revival(root):
    d=root/"real.db";origin(d,0)
    s=snap(d,AKEY,1)
    # Distinct authoritative incarnation can reuse revision values after re-setup.
    d2=root/"rebuilt.db";origin(d2,1)
    with closing(source.open_station(d2)) as c:
        c.execute("update source_identity set id='rebuilt'")
    ok,x,_=age(d2,s,AKEY,1)
    assert not ok and s[3]==x[3] and s[2]!=x[2]
    assert not age(d,s,BKEY,1)[0]
    with closing(source.open_station(d,)) as c:
        c.execute("update generation set rev=? where scope='log'",(2**63-1,))
        # Jump only in the test to the int maximum; an attempted next tick is atomic.
        c.execute("insert into generation values('log','*',?) on conflict do nothing",(2**63-1,))
    try:op(d,AKEY,1)
    except sqlite3.IntegrityError:pass
    else:raise AssertionError("wrap escaped")
    assert snap(d,AKEY,1)[1]=="pending"

def replace_control(root):
    d=root/"restrict.db";origin(d,0)
    assert op(d,AKEY,1)["status"]=="applied"
    cached=snap(d,AKEY,1)
    with closing(source.open_station(d)) as c:
        c.execute("pragma recursive_triggers=off")
        r=c.execute("select payload,tick,result from receipt where intent=?",(AKEY,)).fetchone()
        assert r[1]==8
        c.execute("insert or replace into receipt values(?,?,?,?)",("excluded",*r))
        assert view(c,AKEY,1)[0]=="pending"
        # SQLite's excluded conflict replacement does not fire the old-row delete trigger.
        assert all(v(c,*k)==u for k,u in cached[3].items())

def fork_control(root):
    d=root/"old.db";origin(d,0)
    cut=freeze(d,1)
    replies=[]
    # A one-recipient transfer is an assumption. The same portable seal by itself
    # can validate two independently writable destination copies.
    for name in ("first-copy","second-copy"):
        dest=root/(name+".db")
        source.transfer(d,dest)
        assert activate(dest,cut,name)
        replies.append(op(dest,AKEY,2)["status"])
    assert replies==["applied","applied"]
    assert op(d,AKEY,1)["status"]=="refused"

def main():
    records={}
    for s,t,delay,n in product(("after-stage","after-commit"),("after-stage","after-commit"),(False,True),(0,4,12)):
        with tempfile.TemporaryDirectory() as tmp:
            a=exercise(Path(tmp),s,t,delay,n,True)
        with tempfile.TemporaryDirectory() as tmp:
            b=direct(Path(tmp),s,t,delay,n)
        assert a[:4]==b[:4]
        records[f"{s}/{t}/{int(delay)}/{n}"]=[*a,b[4]]
    with tempfile.TemporaryDirectory() as tmp:revival(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:replace_control(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:fork_control(Path(tmp))
    print(json.dumps({"histories":len(records),"rows":records,"scope_controls":["incarnation-alias","subject-alias","overflow","excluded-replace","forked-destination"]},sort_keys=True,separators=(",",":")))
if __name__=="__main__":
    if len(sys.argv)>2:
        assert sys.argv[2]=="worker"
        print(op(Path(sys.argv[3]),sys.argv[4],int(sys.argv[5]),sys.argv[6]))
    else:main()
