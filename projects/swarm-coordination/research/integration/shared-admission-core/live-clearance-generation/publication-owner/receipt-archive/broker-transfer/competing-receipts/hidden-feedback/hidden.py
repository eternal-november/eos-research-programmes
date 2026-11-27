"""Same native archive and settlement with a receiver-local visibility cut."""
from pathlib import Path
from itertools import product
import json,sqlite3,subprocess,tempfile
root=Path(__file__).resolve().parent
A="inspection_100.000002_100.000000_100.000000"
B="inspection_120.000000_100.000000_100.000000"

def select(path,event,stage):
    # Authored mailbox at the actual observed bound receive cut, with the
    # preinstalled current-code interpretation as in the parent fixture.
    with sqlite3.connect(path) as d:
      d.execute("create table ingress(k text primary key, source text, code text)")
      if stage and event["deposited"]=="AA":
        d.execute("insert into ingress values (?,?,?)",(A,"P","AA"))
    with sqlite3.connect(path) as d:
      return d.execute("select * from ingress where k=? and source=? and code=?",(A,"P","AA")).fetchone() is not None

def run(path,kind,read,order):
  with subprocess.Popen([str(root/"score"),"two","exact","exact"],stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE,text=True) as score:
    proof=json.loads(score.stdout.readline())
    assert (proof["A"],proof["B"],proof["A_key"],proof["B_key"])==(1,1,A,B)
    # Persist the producer's exact old archive as a separate layer.
    with sqlite3.connect(path/"source.db") as d:
        d.execute("create table source (id text primary key)")
        for i in (A,B):d.execute("insert into source values (?)",(i,))
    with sqlite3.connect(path/"source.db") as d:
        codes="".join(k for k,i in (("A",A),("B",B)) if d.execute("select 1 from source where id=?",(i,)).fetchone())
    with subprocess.Popen([str(root/"hidden"),"2","3","4","4","5",order,
             "P" if kind=="lost" else "none",kind],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as r:
      r.stdin.write(codes+"\n");r.stdin.flush()
      assert json.loads(r.stdout.readline())=={"A_copies":2,"B_copies":1}
      after,_=score.communicate("next\n",timeout=5)
      assert score.returncode==0 and json.loads(after)=={"closed":1,"independent":1}
      r.stdin.write("closed\n");r.stdin.flush()
      cut=json.loads(r.stdout.readline())
      recovered=select(path/"sink.db",cut,read)
      row,_=r.communicate("recovered\n" if recovered else "none\n",timeout=5)
      assert r.returncode==0
  return cut,recovered,json.loads(row)

def check(out,kind,read,order):
  cut,recovered,res=out
  visible=kind=="exposed"; arrival=kind!="lost"
  expect="AX" if kind=="stale" else "AA" if arrival else ""
  assert cut=={"deposited":expect,"app":int(visible),"rx":2*int(arrival)}
  assert recovered==(read and expect=="AA")
  paid=visible or recovered
  rx=cut["rx"]; raw="P" if arrival else ""; attempted=raw; tx=rx; b=0
  for s in ("RQ" if order=="Bfirst" else "QR"):
    if s=="Q" and paid:continue
    size=2 if s=="Q" else 3
    cap=4 if s=="Q" else 5
    attempted+=s;tx+=size
    if rx+size<=cap:
      rx+=size;raw+=s
      if s=="Q":paid=True
      else:b=1
  assert res=={"A":int(paid),"B":b,"arrivals":raw,"attempts":attempted,"rx":rx,"tx":tx,"side":1}

out={}
for k,m,o in product(("lost","exposed","hidden","stale"),(False,True),("Qfirst","Bfirst")):
  with tempfile.TemporaryDirectory() as h: v=run(Path(h),k,m,o)
  check(v,k,m,o)
  out[f"{k}/{int(m)}/{o}"]=v
assert out["hidden/0/Qfirst"][-1]["B"]==0
assert out["hidden/1/Qfirst"][-1]["B"]==1
assert out["hidden/1/Qfirst"][-1]["attempts"]=="PR"
assert out["stale/1/Qfirst"][0]["rx"]==out["hidden/1/Qfirst"][0]["rx"]
assert not out["stale/1/Qfirst"][1]
print(json.dumps(out,sort_keys=True))
