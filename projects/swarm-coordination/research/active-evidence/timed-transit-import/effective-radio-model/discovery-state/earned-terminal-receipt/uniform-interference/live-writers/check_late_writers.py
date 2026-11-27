from pathlib import Path
from itertools import product
import json,subprocess
from replay import inputs
ROOT=Path(__file__).parent

def expect(order,where,guard,q,b):
    A=B=txP=txQ=noP=noQ=rx=0
    cached=False
    def primary():
        nonlocal noP,txP,rx,A
        if (guard=="all-inline" and A) or (guard=="all-stale" and cached):
            noP+=1;return
        txP+=9
        if order=="ba":
            assert rx+9<=32
            A+=1;rx+=9
    if where=="prefix":primary()
    cached=bool(A)
    if where=="gap":primary()
    if (guard in ("Q-snapshot","all-stale") and cached) or (guard in ("Q-inline","all-inline") and A):
        noQ+=1
    elif q>=9:
        txQ+=9
        if rx+9<=q:rx+=9;A+=1
    if where=="second":primary()
    if rx+10<=b:B=1;rx+=10
    if where=="after":primary()
    return (A,B,int(cached),noP,noQ,txP,txQ,rx,1)

def main():
    g,x,d=inputs()
    ids=(3,2,39)
    pts=(x[3],x[39],(49,50,0),(51,50,0))
    seed="1\n"+" ".join(map(str,(*ids,*(d[i][j] for i in ids for j in ids),
                                 *(n for p in pts for n in p),25.51)))+"\n"
    modes=("none","Q-snapshot","Q-inline","all-inline","all-stale")
    spots=("prefix","gap","second","after")
    report={}; checks=0
    for order,where,guard,q,b in product(("ab","ba"),spots,modes,(17,18,19),(18,19,27,28)):
        native=subprocess.run([str(ROOT/"late_writers"),str(q),str(b),order,where,guard],
                              input=seed,text=True,capture_output=True,check=True).stdout
        got=tuple(map(int,native.split()))
        assert got==expect(order,where,guard,q,b),(order,where,guard,q,b,got)
        if (q,b)==(18,19):report[f"{order}/{where}/{guard}"]=got
        checks+=1
    for guard in modes:
        assert all(report[f"ab/{p}/{guard}"][:2]==(1,1) for p in spots)
    for guard,answers in {
        "none":(0,0,0,1),"Q-snapshot":(1,0,0,1),"Q-inline":(1,1,0,1),
        "all-inline":(1,1,1,1),"all-stale":(1,0,0,1),
    }.items():
        assert tuple(report[f"ba/{p}/{guard}"][1] for p in spots)==answers
    print(json.dumps({"runs":checks,"controls":report},sort_keys=True))
if __name__=="__main__":main()
