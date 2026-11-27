"""Pilot: exclusive recipient choice and its service limits on a single SQLite registry."""
from contextlib import closing
from itertools import product
from pathlib import Path
import json
import os
import sqlite3
import subprocess
import sys
import tempfile
import overlap as model
from trace_queries import source

def claim(reg,transfer,recipient,phase="none"):
    with closing(sqlite3.connect(reg,isolation_level=None)) as c:
        c.execute("begin immediate")
        c.execute("insert into selected values(?,?) on conflict(transfer) do nothing",(transfer,recipient))
        winner=c.execute("select recipient from selected where transfer=?",(transfer,)).fetchone()[0]
        if phase=="before-commit":os._exit(78)
        c.commit()
        if phase=="after-commit":os._exit(78)
        return winner==recipient

def winner(reg,x):
    with closing(sqlite3.connect(reg)) as c:
        row=c.execute("select recipient from selected where transfer=?",(x,)).fetchone()
        return None if row is None else row[0]

def prepare(root):
    src=root/"source.db";model.origin(src,0)
    cut=model.freeze(src,1)
    ids=("shop-west","shop-east")
    dst={i:root/(i+".db") for i in ids}
    for p in dst.values():source.transfer(src,p)
    reg=root/"registry.db"
    with closing(sqlite3.connect(reg,isolation_level=None)) as c:
        c.execute("pragma journal_mode=WAL")
        c.execute("pragma synchronous=full")
        c.execute("create table selected(transfer text primary key,recipient text not null)")
    return src,cut,dst,reg,ids

def install(dst,reg,transfer,cut,identity):
    # This parameter stands for a trusted executor-local identity, not a caller-provided name.
    return winner(reg,transfer)==identity and model.activate(dst,cut,identity)

def worker_cmd(reg,t,id,phase):
    return [sys.executable,"-B",__file__,sys.argv[1],"claim",str(reg),t,id,phase]
def crash_claim(reg,t,id,phase):
    r=subprocess.run(worker_cmd(reg,t,id,phase),text=True,capture_output=True)
    assert r.returncode==78 and r.stdout=="",r

def crash_cut(root,phase,first):
    src,cut,dst,reg,ids=prepare(root)
    p,q=ids if first else ids[::-1]
    transfer="station:1"
    crash_claim(reg,transfer,p,phase)
    want=q if phase=="before-commit" else p
    assert claim(reg,transfer,q)==(want==q)
    assert claim(reg,transfer,p)==(want==p)
    wins=[i for i in ids if install(dst[i],reg,transfer,cut,i)]
    assert wins==[want]
    o=model.op(dst[want],model.AKEY,2)
    assert o["status"]=="applied"
    assert model.op(dst[want],model.AKEY,2)["status"]=="cached"
    assert model.op(src,model.AKEY,1)["status"]=="refused"
    assert model.op(dst[q if want==p else p],model.AKEY,2)["status"]=="refused"

def concurrent(root):
    src,cut,dst,reg,ids=prepare(root)
    t="station:1"
    ps=[subprocess.Popen(worker_cmd(reg,t,i,"none"),stdout=subprocess.PIPE,text=True) for i in ids]
    replies=[p.communicate(timeout=30)[0].strip() for p in ps]
    assert sorted(replies)==["false","true"] and all(p.returncode==0 for p in ps)
    chosen=winner(reg,t)
    assert install(dst[chosen],reg,t,cut,chosen)
    peer=next(i for i in ids if i!=chosen)
    assert not install(dst[peer],reg,t,cut,peer)
    assert model.op(dst[chosen],model.AKEY,2)["status"]=="applied"

def stale_append(root):
    src,cut,dst,reg,(a,b)=prepare(root); t="station:1"
    assert claim(reg,t,a) and install(dst[a],reg,t,cut,a)
    # There is no later authority transition in the positive protocol. A
    # forced reassignment tests why an allocator decision alone is insufficient.
    with closing(sqlite3.connect(reg,isolation_level=None)) as c:
        c.execute("update selected set recipient=? where transfer=?",(b,t))
    assert install(dst[b],reg,t,cut,b)
    assert model.op(dst[b],model.AKEY,2)["status"]=="applied"
    assert model.op(dst[a],model.AKEY,2)["status"]=="applied"
    return "two commits if selection is overwritten without fencing the prior installer"

def main():
    for phase,f in product(("before-commit","after-commit"),(False,True)):
        with tempfile.TemporaryDirectory() as d:crash_cut(Path(d),phase,f)
    for _ in range(4):
        with tempfile.TemporaryDirectory() as d:concurrent(Path(d))
    with tempfile.TemporaryDirectory() as d:lim=stale_append(Path(d))
    print(json.dumps({"crash_cuts":4,"race_runs":4,"admitted_native_effects_each":1,"excluded_reassignment":lim},sort_keys=True))
if __name__=="__main__":
    if len(sys.argv)>2:
        assert sys.argv[2]=="claim"
        print(json.dumps(claim(*sys.argv[3:7])))
    else:main()
