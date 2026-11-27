from itertools import combinations,product
from pathlib import Path
from collections import Counter
import json,subprocess
from replay import inputs
ROOT=Path(__file__).parent

def canonical(n):
    def go(seed):
        if len(seed)==n:yield ''.join(map(str,seed));return
        for tag in range(max(seed)+2):yield from go(seed+(tag,))
    return tuple(go((0,)))

def main():
    g,x,d=inputs()
    ids=(3,2,39);pts=(x[3],x[39],(49,50,0),(51,50,0))
    arg="1\n"+" ".join(map(str,(*ids,*(d[i][j] for i in ids for j in ids),
                                   *(v for p in pts for v in p),25.51)))+"\n"
    n=5;edge=list(combinations(range(n),2));tags=canonical(n)
    assert len(edge)==10 and len(tags)==52
    runs=0
    def call(timeline,labels,mode):
        nonlocal runs
        p=subprocess.run([str(ROOT/"receipt_labels"),"28",timeline,labels,mode],input=arg,
                             text=True,capture_output=True,check=True)
        out=tuple(map(int,p.stdout.split()))
        assert len(out)==9 and out[-1]==1
        # Independent ordinary transition reference; update prefix only on
        # successful native ingress; unguarded duplicates spend before B.
        seen=set(); arr=[0]*n; b=skip=rx=0
        for token in timeline:
            if token=='|':
                if mode=='clear':seen.clear()
            elif token=='B':
                if rx+10<=28:b+=1;rx+=10
            else:
                j=int(token)
                ident=token if mode=='qualified' else labels[j]
                if mode!='blind' and ident in seen:skip+=1
                else:
                    rx+=9;arr[j]+=1;seen.add(ident)
        assert out==(*arr,b,skip,rx,1),(timeline,labels,mode,out)
        runs+=1
        return out
    verdict={}
    for tag,((i,j),direction) in product(tags,product(edge,(0,1))):
        if direction:i,j=j,i
        row=call(f"{i}{i}{j}{j}B",tag,"fixed")
        admit=row[i]==row[j]==row[5]==1
        assert admit==(tag[i]!=tag[j])
        verdict[tag,i,j]=admit
    hist=Counter()
    for m in range(1<<len(edge)):
        enabled=tuple((i,j) for k,(i,j) in enumerate(edge) if m>>k&1)
        # Two independent computations of the minimum: from the graph,
        # and from the native per-window acceptance matrix.
        theory=min(len(set(t)) for t in tags if all(t[i]!=t[j] for i,j in enabled))
        check=min(len(set(t)) for t in tags if all(verdict[t,i,j] and verdict[t,j,i] for i,j in enabled))
        assert check==theory
        hist[check]+=1
        if m==(1<<len(edge))-1:assert check==5
    rebind={}
    for mode,tr in product(("keep","clear","qualified","blind"),("0|1B","0|01B","0|10B")):
        row=call(tr,"00000",mode);rebind[mode+"/"+tr]=row
    assert rebind["keep/0|1B"][1]==0
    assert rebind["clear/0|1B"][1]==1
    assert rebind["clear/0|01B"][1]==0
    assert rebind["qualified/0|01B"][:6]==(1,1,0,0,0,1)
    assert rebind["blind/0|01B"][5]==0
    print(json.dumps({"native_rows":runs,"graph_minimum_histogram":hist,"rebind":rebind},sort_keys=True))
if __name__=="__main__":main()
