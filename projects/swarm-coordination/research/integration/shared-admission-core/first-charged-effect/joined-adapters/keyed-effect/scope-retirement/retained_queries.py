#!/usr/bin/env python3
"""Two live native completion records with out-of-order durable receipts."""
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
def pinned(p,sha):
    b=p.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha

def frontier(acks):
    j=0
    while j+1 in acks:j+=1
    return j

def encode(records,acks,width,policy):
    f=max(acks,default=0) if policy=="max" else frontier(acks)
    retired=set(range(1,f+1))
    buf=bytearray([f])
    if policy=="selective":
        holes=acks-retired
        buf.append(sum(1<<(i-1) for i in holes))
        retired|=holes
    for i in (1,2):
        if i not in retired:
            a=records[i]
            buf.extend(bytes(a) if width==4 else bytes([a[0]]))
    return bytes(buf)

def decode(db,wire,width,policy):
    f=wire[0]; out={i:"retired" for i in range(1,f+1)}
    off=1
    if policy=="selective":
        mask=wire[off];off+=1
        out.update({i:"retired" for i in (1,2) if mask&(1<<(i-1))})
    for i in (1,2):
        if i not in out:
            raw=wire[off:off+width]
            assert len(raw)==width
            if width==4:result=list(raw)
            else:
                r=db.execute("select result from motion where tick=?",(raw[0],)).fetchone()
                result=json.loads(r[0])
            out[i]=result
            off+=width
    assert off==len(wire)
    return out

def retry(db,key,scope):
    if scope!=7:return "wrong-scope"
    record=db.execute("select item from recovered where epoch=? and id=?",(scope,key)).fetchone()
    return "unknown" if record is None else json.loads(record[0])

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--warehouse",type=Path,default=HERE/"warehouse")
    p.add_argument("--support",type=Path,default=HERE/"support.py")
    a=p.parse_args()
    jroot=parent("motion_journal.py")
    pinned(jroot/"motion_journal.py","19447b46bd35310370ddd386ed2c29b3a60f60b5")
    pinned(a.support,"b0e6c09b6ba593ccd373371541f0d20a0ff8a414")
    sys.path[:0]=[str(jroot),str(a.support.resolve().parent)]
    import motion_journal as j
    import support
    iso,n=support.load(a.warehouse.resolve())
    plant=j.Plant(iso,n)
    with tempfile.TemporaryDirectory() as directory:
        root=Path(directory); donor=j.connect(root/"donor")
        records={}
        for i,k in enumerate((j.OLD,j.SAME_PHYSICAL_UNRELATED),1):
            how,row=j.apply(donor,plant,k,i-1)
            assert how=="new" and row==[i,i-1,2,i]
            records[i]=row
        assert j.apply(donor,plant,None,3)==("new",[3,3,3,4])
        native=plant.native(donor)
        before=plant.snapshot(native)
        rows=list(donor.execute("select * from motion order by tick"))
        donor.close()
        results={}
        for bits in product((False,True),repeat=2):
            sender=j.connect(root/"client")
            sender.execute("create table if not exists exact(id integer primary key,value text)")
            sender.execute("delete from exact")
            for i in (1,2):
                if bits[i-1]:sender.execute("insert into exact values (?,?)",(i,j.enc(records[i])))
            sender.close() # durable receipt, not a forecast or an application callback
            sender=j.connect(root/"client")
            acks={i for i,value in sender.execute("select * from exact") if json.loads(value)==records[i]}
            sender.close()
            assert acks=={i for i in (1,2) if bits[i-1]}
            for width,policy in product((1,4),("contiguous","selective","max")):
                packet=encode(records,acks,width,policy)
                replacement=j.connect(root/"replacement")
                replacement.execute("delete from motion")
                replacement.executemany("insert into motion values (?,?,?)",rows)
                assert plant.snapshot(plant.native(replacement))==before
                table=decode(replacement,packet,width,policy)
                replacement.execute("create table if not exists recovered(epoch integer,id integer,item text,primary key(epoch,id))")
                replacement.execute("begin immediate")
                replacement.execute("delete from recovered")
                replacement.executemany("insert into recovered values (7,?,?)",
                                        [(i,j.enc(item)) for i,item in table.items()])
                replacement.commit()
                replacement.close()
                replacement=j.connect(root/"replacement")
                # Same late query interface after reopen, with no donor or client handle.
                assert all(retry(replacement,i,6)=="wrong-scope" for i in (1,2))
                legal=True
                for i in (1,2):
                    got=retry(replacement,i,7)
                    if i not in acks:legal &= got==records[i]
                    else:assert got=="retired" or got==records[i]
                # The benchmark cannot resolve any old retry by reissuing a move.
                assert plant.snapshot(plant.native(replacement))==before
                assert bool(legal)==(policy!="max" or acks!={2})
                results[f"{''.join(str(int(x)) for x in bits)}/{width}/{policy}"]=[len(packet),bool(legal),table]
                replacement.close()
        assert [results[f"01/4/{p}"][0] for p in ("contiguous","selective")]==[9,6]
        assert [results[f"01/1/{p}"][0] for p in ("contiguous","selective")]==[3,3]
        # Fix the frontier before enumerating the remaining independent statuses.
        classes={str(n):len(set(product((0,1),repeat=n))) for n in (8,9)}
        assert classes=={"8":256,"9":512}
        print(json.dumps({"arms":len(results),"classes":classes,"witness":{k:v for k,v in results.items() if k.startswith("01/")}},sort_keys=True))
if __name__=="__main__":main()
