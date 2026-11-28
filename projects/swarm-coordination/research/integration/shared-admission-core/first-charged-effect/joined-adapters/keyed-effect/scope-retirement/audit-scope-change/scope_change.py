#!/usr/bin/env python3
"""A change in allowed queries after an acknowledged old result is retired."""
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tempfile

HERE=Path(__file__).resolve().parent

def parent(name):
    return next(p for p in (HERE,*HERE.parents) if (p/name).is_file())
def pin(p,sha):
    b=p.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    base=parent("motion_journal.py")
    pin(base/"motion_journal.py","19447b46bd35310370ddd386ed2c29b3a60f60b5")
    pin(a.support,"b0e6c09b6ba593ccd373371541f0d20a0ff8a414")
    sys.path[:0]=[str(base),str(a.support.resolve().parent)]
    import motion_journal as j
    import support
    iso,n=support.load(a.warehouse.resolve()); plant=j.Plant(iso,n)
    with tempfile.TemporaryDirectory() as d:
        root=Path(d)
        histories=[]
        for h in (0,1):
            source=j.connect(root/f"d{h}")
            for actor in (0,1):
                key=j.OLD if actor==h else j.SAME_PHYSICAL_UNRELATED
                assert j.apply(source,plant,key,actor)==("new",[actor+1,actor,2,actor+1])
            kind,current=j.apply(source,plant,None,3)
            assert kind=="new" and current==[3,3,3,4]
            old=j.resolved(source,j.OLD)
            assert old==[h+1,h,2,h+1]
            raw=list(source.execute("select * from motion order by tick"))
            source.close()
            # Account for exact native receipt becoming durably acknowledged
            # at a separate client before server-side retirement. That client
            # is not connected to any replacement query below.
            client=j.connect(root/f"client{h}")
            client.execute("create table acknowledgements(receipt text)")
            client.execute("insert into acknowledgements values (?)",(j.enc(old),))
            client.close()
            client=j.connect(root/f"client{h}")
            assert json.loads(client.execute("select receipt from acknowledgements").fetchone()[0])==old
            client.close()
            histories.append((raw,current,old))
        assert histories[0][:2]==histories[1][:2] and histories[0][2]!=histories[1][2]
        out={}
        for h,method,observer in product((0,1),("retired","ordinal","full","stale"),("retry","audit")):
            raw,current,old=histories[h]
            path=root/f"r{h}-{method}-{observer}"
            replacement=j.connect(path)
            replacement.executemany("insert into motion values (?,?,?)",raw)
            replacement.execute("create table export(witness_scope integer,kept text,terminal integer,witness blob)")
            payload={"retired":b"","ordinal":bytes([h]),"full":bytes(old),"stale":bytes([h])}[method]
            scope=6 if method=="stale" else 7
            replacement.execute("insert into export values (?,?,?,?)",(scope,j.enc(current),1,payload))
            replacement.close()
            replacement=j.connect(path)
            # The replacement only reads its own durable state. The audit
            # role is granted at the new cut, without changing any motion.
            sr,kept,terminal,w= replacement.execute("select * from export").fetchone()
            assert kept==j.enc(current) and terminal
            if observer=="retry": answer="terminal"
            elif sr!=7 or not w:answer="unavailable"
            elif method=="ordinal":
                assert len(w)==1 and w[0] in (0,1)
                actor_rows=tuple(x[0] for x in replacement.execute("select actor from motion order by tick"))
                assert actor_rows==(0,1,3)
                answer=json.loads(replacement.execute("select result from motion where tick=?",(w[0]+1,)).fetchone()[0])
            else:answer=list(w)
            assert plant.native(replacement)._cur_steps==3
            if observer=="retry":assert answer=="terminal"
            elif method in ("ordinal","full"):assert answer==old
            else:assert answer=="unavailable"
            out[f"{h}/{method}/{observer}"]=answer
            replacement.close()
        print(json.dumps({"cases":len(out),"same_raw_motion":True,
             "answers":out,"exact_required":[h[2] for h in histories]},sort_keys=True))
if __name__=="__main__":main()
