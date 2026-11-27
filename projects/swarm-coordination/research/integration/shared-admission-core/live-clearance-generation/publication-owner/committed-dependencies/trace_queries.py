"""Trace the unmodified authorized_step query paths using interpreter-side SQLite observation."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile

from types import ModuleType
p=Path(__file__).with_name("replay.py")
b=p.read_bytes()
assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()=="13356cc4054027020aeb4b2f204e3d738286cbe4"
text=b.decode()
delimiter='\nif len(sys.argv)>2 and sys.argv[2]=="fencer":'
assert text.count(delimiter)==1
source=ModuleType("serialized_station")
# Skip only the upstream command-line dispatch; all callable bodies stay byte-identical.
exec(compile(text.split(delimiter)[0],str(p),"exec"),source.__dict__)

raw_open=source.open_station
path=[]
def observed(db):
    conn=raw_open(db)
    conn.set_trace_callback(lambda statement:path.append(statement.strip().lower()))
    return conn

def one(root,kind):
    db=root/(kind+".db")
    source.init(db,kind!="no-permit")
    if kind=="hit":
        assert source.authorized_step(db,1,"none")["status"]=="applied"
    if kind=="fenced":
        source.fence(db)
    source.open_station=observed
    try:
        path.clear()
        r=source.authorized_step(db,1,"none")
    finally: source.open_station=raw_open
    data=[s for s in path if s.startswith("select")]
    return kind,r["status"],data

def main():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp)
        records=[one(root,k) for k in ("no-permit","fenced","miss","hit")]
    assert [x[1] for x in records]==["refused","refused","applied","cached"]
    for kind,_,qs in records:
        assert ["from permit" in qs[0],"from authority" in qs[1]]==[True,True]
        assert any("from log" in q for q in qs)==(kind=="miss")
        assert any("from receipt" in q for q in qs)==(kind in ("miss","hit"))
    print(json.dumps(records,separators=(",",":")))
if __name__=="__main__":
    main()
