
"""Run the unchanged one-cut checker against actual source-facing controls."""
from pathlib import Path
import sqlite3,subprocess,tempfile,json
from itertools import product
from core import Row,Event,Use,admitted

root=Path(__file__).resolve().parent
A="inspection_100.000002_100.000000_100.000000"
B="inspection_120.000000_100.000000_100.000000"
RX=("Scout","rx")
def compose(raw,already,observed):
  before=(Event(0,0,uses=(Use(RX,raw,5,4),) if raw else (),
                paid=("A",) if already else ()),)
  def output(order):
    r=raw;has=already;e=[]
    for i,w in enumerate(order):
      if w=="Q" and already:continue
      n,cap,k=(2,4,"A") if w=="Q" else (3,5,"B")
      use=[Use((w,"tx"),n,cap,4)]
      deliver=r+n<=cap
      received=()
      if deliver:
        use.append(Use(RX,n,cap,4));r+=n
        if k=="B" or not has:received=(k,)
        if k=="A":has=True
      e.append(Event(1,i,uses=tuple(use),paid=received))
    return tuple(e)
  return Row(((0,"Scout",observed),),frozenset(),before,
             {p:output(seq) for p,seq in (("B","R"),("QB","QR"),("BQ","RQ"))})

def choices():
  # Exactly scoped observation, not the posterior evaluator's state.
  rows=[compose(2,True,"positive"),compose(0,False,"before-cut-removal"),
        compose(0,False,"ambiguous"),compose(2,False,"ambiguous")]
  both=admitted(rows,"Scout",1,{"A":1,"B":1},["B","QB","BQ"])
  projected=[r for r in rows if r.receipts[0][2]!="positive"]
  b=admitted(projected,"Scout",1,{"B":1},["B","QB","BQ"])
  def only(source):return {v[0][1]:o for v,o in source.items()}
  return only(both),only(b)

def live(path,kind,mailbox,cert,both,fallback):
  with subprocess.Popen([str(root/"score"),"two","exact","exact"],stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE,text=True) as score:
    proof=json.loads(score.stdout.readline())
    assert (proof["A"],proof["B"],proof["A_key"],proof["B_key"])==(1,1,A,B)
    with sqlite3.connect(path/"source.db") as d:
      d.execute("create table source (id text primary key)")
      for i in (A,B):d.execute("insert into source values (?)",(i,))
    with sqlite3.connect(path/"source.db") as d:
      codes="".join(k for k,i in (("A",A),("B",B)) if d.execute("select 1 from source where id=?",(i,)).fetchone())
    with subprocess.Popen([str(root/"native"),"2","3","4","4","5","core",
             "P" if kind=="lost" else "none",kind],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as r:
      r.stdin.write(codes+"\n");r.stdin.flush()
      assert json.loads(r.stdout.readline())=={"A_copies":2,"B_copies":1}
      after,_=score.communicate("next\n",timeout=5)
      assert score.returncode==0 and json.loads(after)=={"closed":1,"independent":1}
      r.stdin.write("closed\n");r.stdin.flush()
      cut=json.loads(r.stdout.readline())
      with sqlite3.connect(path/"sink.db") as d:
        d.execute("create table ingress (k text primary key, source text, code text)")
        if mailbox and cut["deposited"]=="AA":d.execute("insert into ingress values (?,?,?)",(A,"P","AA"))
      with sqlite3.connect(path/"sink.db") as d:
        recovery=d.execute("select * from ingress where k=? and source=? and code=?",(A,"P","AA")).fetchone() is not None
      # No received-byte total or hidden world label in the action interface.
      obs="positive" if recovery or cut["app"] else (
          "before-cut-removal" if cert and cut["pre_removed"] else "ambiguous")
      pick={"positive":"B","before-cut-removal":"QB","ambiguous":"B"}[obs]
      selected=both[obs]
      assert pick in (selected if selected else fallback[obs])
      raw,_=r.communicate(("recovered" if recovery else "none")+"\n"+pick+"\n",timeout=5)
      assert r.returncode==0
      result=json.loads(raw)
      assert result["B"]==1 and result["side"]==1
      assert result["A"]==bool(selected)
      return {"obs":obs,"admission":list(selected),"action":pick,"result":result}

def main():
    full,b=choices()
    assert full["positive"] and full["before-cut-removal"]==("QB",) and not full["ambiguous"]
    assert "B" in b["ambiguous"]
    out={}
    for world,mail,cert in product(("lost","hidden","stale","exposed"),(False,True),(False,True)):
        with tempfile.TemporaryDirectory() as h: out[f"{world}/{int(mail)}/{int(cert)}"]=live(Path(h),world,mail,cert,full,b)
    print(json.dumps({"full":full,"cases":out},sort_keys=True))
if __name__=="__main__":main()
