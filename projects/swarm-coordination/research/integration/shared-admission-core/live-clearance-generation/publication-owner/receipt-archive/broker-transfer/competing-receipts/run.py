from itertools import product,permutations
from pathlib import Path
import sqlite3,subprocess,tempfile,json
from collections import Counter
root=Path(__file__).resolve().parent
expected={"A":"inspection_100.000002_100.000000_100.000000",
          "B":"inspection_120.000000_100.000000_100.000000"}
def go(db,scope,a,b,caps,order,gone):
  with subprocess.Popen([str(root/"score"),"two",*("exact" if i in scope else "sibling" for i in "AB")],
                         stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as score:
    x=json.loads(score.stdout.readline()); assert x["score"]==2
    with sqlite3.connect(db) as d:
      d.execute("create table receipts (k text primary key, score int)")
      for i,k in expected.items():
        assert x[i+"_key"]==k
        if x[i]:d.execute("insert into receipts values (?,1)",(k,))
    with sqlite3.connect(db) as d:
      actual="".join(i for i,k in expected.items() if d.execute("select score from receipts where k=?",(k,)).fetchone()==(1,))
    with subprocess.Popen([str(root/"competing"),*(str(n) for n in (a,b,*caps)),order,gone],
                           stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as radio:
      radio.stdin.write(actual+"\n");radio.stdin.flush()
      staged=json.loads(radio.stdout.readline())
      post,_=score.communicate("next\n",timeout=5)
      assert score.returncode==0 and json.loads(post)=={"closed":1,"independent":1}
      msg,_=radio.communicate("closed\n",timeout=5)
      assert radio.returncode==0
  assert actual==scope
  assert staged=={"A_copies":2*int("A" in actual),"B_copies":int("B" in actual)}
  row=json.loads(msg)
  rx=0; tx=0; arr=""; attempted=""
  for p in ("PQR" if order=="feedback" else order):
    if order=="feedback" and p=="Q" and "P" in arr:continue
    k="B" if p=="R" else "A"
    if p==gone or k not in scope:continue
    attempted+=p
    size=a if k=="A" else b
    if size<=caps["PQR".index(p)]:tx+=size
    if rx+size<=caps["PQR".index(p)]:rx+=size;arr+=p
  assert row=={"A":int('P'in arr or 'Q'in arr),"B":int('R'in arr),"arrivals":arr,
               "attempts":attempted,"rx":rx,"tx":tx,"side":1}, (row,a,b,caps,order,gone)
  return row

def main():
  out=Counter();focus={}
  orders=["".join(p) for p in permutations("PQR")]+["feedback"]
  config=[(n,n,n) for n in range(3,11)]+[(4,4,5),(4,6,5),(5,7,5),(7,5,6),(5,7,10)]
  for (a,b),cap,order,gone,which in product(
      ((3,2),(2,2),(2,3)),config,orders,("none","P","Q","R"),("AB","A","B","")):
    with tempfile.TemporaryDirectory() as h: row=go(Path(h)/"a.db",which,a,b,cap,order,gone)
    out.update(cases=1,both=int(row["A"] and row["B"]),independent=row["side"])
    if (a,b)==(3,2) and cap in ((5,5,5),(6,6,6),(7,7,7),(8,8,8)) and \
      which=="AB" and order in ("PQR","PRQ") and gone in ("none","P"):
      focus[f"{cap[0]}/{order}/{gone}"]=row
    if (a,b)==(2,3) and cap==(4,4,5) and which=="AB" and gone!="R":
      focus[f"weak/{order}/{gone}"]=row
  for order in orders:
    results=[focus[f"weak/{order}/{z}"] for z in ("none","P","Q")]
    assert all(x["A"] and x["B"] for x in results)==(order=="feedback")
  assert [focus[f"{x}/PQR/none"]["B"] for x in (5,6,7,8)]==[1,0,0,1]
  assert all(focus[f"{x}/PRQ/{z}"]["B"] and focus[f"{x}/PRQ/{z}"]["A"]
             for x in (5,6,7,8) for z in ("none","P"))
  print(json.dumps({"summary":out,"witness":focus},sort_keys=True))
if __name__=="__main__":main()
