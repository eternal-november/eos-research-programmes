"""Native common-ingress nonmonotonicity with a physically earned retry permit."""
from pathlib import Path
from collections import deque
from itertools import product
import json,sqlite3,subprocess,tempfile
from replay import inputs
HERE=Path(__file__).parent
A="IR:3/run7"; B="IER:1/run7"; sizes=(len(A),len(B))
DOCK,GATE,START,INSPECT,OUT=39,2,43,1,0

def native(graph_coords,dists,a_order,q,b,expiry,chooser,filter='none'):
    ids=(3,2,39)
    pts=[graph_coords[3],graph_coords[39],(49,50,0),(51,50,0)]
    init="1\n"+" ".join(map(str,(*ids,*(dists[i][j] for i in ids for j in ids),
                                  *(v for x in pts for v in x),25.51)))+"\n"
    child=subprocess.Popen([str(HERE/"gate_budget"),str(q),str(b),a_order,expiry,filter],
                           stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    child.stdin.write(init);child.stdin.flush()
    payload,tx,rx=child.stdout.readline().split()
    assert payload in ("-",A) and int(tx)==len(A)
    observed=int(payload==A)
    assert int(rx)==len(A)*observed
    with tempfile.TemporaryDirectory() as loc:
        path=Path(loc)/"dock.sqlite"
        with sqlite3.connect(path) as conn:
            conn.execute("CREATE TABLE sealed (named_body TEXT PRIMARY KEY)")
            conn.execute("INSERT INTO sealed VALUES('IR:3/prior')")
            if payload==A:conn.execute("INSERT INTO sealed VALUES(?)",(payload,))
        # The chooser sees an interface to the closed dock and must arrive
        # physically before reading, not the source's actual RX counter.
        def lookup(tile):
            assert tile==DOCK
            with sqlite3.connect(path) as conn:
                return conn.execute("SELECT 1 FROM sealed WHERE named_body=?",(A,)).fetchone() is not None
        cmd,meta=chooser(lookup)
        raw,_=child.communicate(cmd+"\n",timeout=20)
    assert child.returncode==0
    row=tuple(map(int,raw.split()))
    assert len(row)==6 and row[-1]==1
    return observed,cmd,meta,row

def result(paid,cmd,q,b,same,filter='none'):
    a,n=sizes
    counts={"A":int(paid),"B":0}
    if filter=="family" or filter=="exact" and paid:cmd=cmd.replace("Q","")
    amount=a*paid
    old_live=True
    for c in cmd:
        size,cap,key=(a,q,"A") if c=="Q" else (n,b,"B")
        if size<=cap and old_live and not same:
            amount-=a*paid
            old_live=False
        if size<=cap and amount+size<=cap:
            counts[key]+=1
            amount+=size
    return (counts["A"],counts["B"],a*int("Q" in cmd and a<=q),n*int(n<=b),amount,1)

def meets(row):
    return row[0]>=1 and row[1]==1

def prefixes(g,cut,query):
    q=deque([(START,0,False,())]);seen={(START,0,False)}
    best={}
    while q:
        tile,t,read,path=q.popleft()
        if tile==DOCK:best.setdefault(("read" if read else "blind","arrived"),(t,path))
        if t>=cut+2:continue
        actions=[(n,read,"move") for n in sorted(g[tile])
                 if (tile,n)!=(DOCK,GATE) or t<cut]
        if tile==DOCK and query and not read:actions.append((tile,True,"read"))
        for n,k,operation in actions:
            step=(t,tile,n,operation)
            if (n,t+1,k) not in seen:
                seen.add((n,t+1,k));q.append((n,t+1,k,path+(step,)))
            if (tile,n)==(DOCK,GATE):best.setdefault(("read" if k else "blind","permit"),(t+1,path+(step,)))
    return best

def suffix(g,pos,done):
    path=[]
    for dest in (INSPECT,OUT):
        q=deque([(pos,())]);seen={pos}
        while q:
            u,tr=q.popleft()
            if u==dest:break
            for z in sorted(g[u]):
                if z in seen:continue
                # Departing publicly after the latest cut; return direction is
                # unaffected. No issued authority is banked for a new send.
                if (u,z)==(DOCK,GATE):continue
                seen.add(z);q.append((z,tr+((u,z),)))
        else:raise ValueError("egress lost")
        for a,b in tr:path.append((done,a,b,"move"));done+=1
        pos=dest
        if dest==INSPECT:path.append((done,dest,dest,"inspect"));done+=1
    assert done<=12
    return path,done

def describe(g,cut,mode,q,b,same):
    options=prefixes(g,cut,mode!="none")
    schema={}
    for reading in (False,True):
        if reading and mode=="none":continue
        tag="read" if reading else "blind"
        views=(("absent","present") if mode=="sealed" else ("unknown",)) if reading else ("unknown",)
        menu=("B",)+(("QB","BQ") if (tag,"permit") in options else ())
        cells={}
        for v in views:
            states=(False,) if v=="absent" else (True,) if v=="present" else (False,True)
            full=[a for a in menu if all(meets(result(p,a,q,b,same)) for p in states)]
            # If uniform service is impossible, protect B if possible.
            protect=[a for a in menu if all(result(p,a,q,b,same)[1] for p in states)]
            if full:pick=full[0]
            elif protect:pick=protect[0]
            else:pick="B"
            cells[v]=(bool(full),pick)
        schema[reading]=cells
    best=min(schema,key=lambda r:(not all(v[0] for v in schema[r].values()),r))
    return best,schema[best],options

def main():
    graph,coords,dists=inputs()
    grid={};native_cases=0
    for q,b,expiry,order,cmd in product((8,9,17,18,19),(9,10,18,19,20,27,28),
                                        ("closed","past"),("ab","ba"),("B","QB","BQ")):
        got,actions,_,row=native(coords,dists,order,q,b,expiry,lambda lk:(cmd,None))
        assert (got==1)==(order=="ba") and actions==cmd
        assert row==result(got==1,cmd,q,b,expiry=="closed"),(q,b,expiry,order,cmd,row)
        grid[q,b,expiry,order,cmd]=meets(row)
        native_cases+=1
    # Independently check symbolic threshold on the declared same native cut.
    a,n=sizes
    for q,b in product((8,9,17,18,19),(9,10,18,19,20,27,28)):
        want=b>=a+n and ((q>=a and (q<2*a or b>=2*a+n)) or q>=a+n)
        assert want==any(all(grid[q,b,"closed",o,c] for o in ("ab","ba"))
                         for c in ("B","QB","BQ"))
    routes={};archive_summary={};admitted=0
    for cut,mode,q,b,expiry in product((1,2,3,4),("none","unavailable","sealed"),
                                        (17,18,19),(18,19,27,28),("closed","past")):
        read,views,prefix=describe(graph,cut,mode,q,b,expiry=="closed")
        whole=all(x[0] for x in views.values());admitted+=int(whole)
        if cut>=3:
            if mode=="none":assert ("read","permit") not in prefix
            else:assert prefix["read","permit"][0]==3
        key=f"{cut}/{mode}/{q}/{b}/{expiry}"
        archive_summary[key]=[whole,read,views]
        # Finite plant shape: no view, one exact lookup or an unavailable lookup.
        # Any additional query at an unchanged sealed dock cannot refine it.
        for order in ("ab","ba"):
            def select(lookup):
                tag="read" if read else "blind"
                if read:
                    t,path=prefix[(tag,"arrived")]
                    assert path and path[-1][3]=="read"
                    if mode=="sealed":
                        known=lookup(path[-1][1])
                        obs="present" if known else "absent"
                    else:obs="unknown"
                else:
                    t,path=prefix[(tag,"arrived")]
                    obs="unknown"
                ok,cmd=views[obs]
                if "Q" in cmd:
                    s,p=prefix[(tag,"permit")]
                    assert p[:len(path)]==path and p[-1][:3]==(s-1,DOCK,GATE) and s-1<cut
                    t,path,loc=s,p,GATE
                else:loc=DOCK
                remaining,end=suffix(graph,loc,t)
                return cmd,[obs,ok,(*path,*remaining),end]
            good,cmd,meta,row=native(coords,dists,order,q,b,expiry,select)
            assert row==result(bool(good),cmd,q,b,expiry=="closed")
            if whole or meta[1]:assert meets(row)
            if (q,b,expiry)==(18,19,"closed") and cut in (2,3):
                routes[f"{cut}/{mode}/{order}"]=[cmd,meta,row]
            native_cases+=1
    assert archive_summary["3/sealed/18/19/closed"][0]
    assert not archive_summary["2/sealed/18/19/closed"][0]
    assert not archive_summary["3/unavailable/18/19/closed"][0]
    assert archive_summary["2/none/17/19/closed"][0]
    assert archive_summary["2/none/19/19/closed"][0]
    assert archive_summary["2/none/18/28/closed"][0]
    assert archive_summary["2/none/18/19/past"][0]
    owner={}
    for cut,order,filter in product((1,2,3),("ab","ba"),("none","exact","family")):
        route=prefixes(graph,cut,False)
        cmd="QB" if ("blind","permit") in route else "B"
        paid,issued,v,row=native(coords,dists,order,18,19,"closed",lambda lk:(cmd,None),filter)
        assert row==result(bool(paid),issued,18,19,True,filter)
        native_cases+=1
        owner[f"{cut}/{order}/{filter}"]=[cmd,row]
    assert all(meets(owner[f"2/{o}/exact"][1]) for o in ("ab","ba"))
    assert not meets(owner["2/ab/family"][1])
    assert not meets(owner["1/ab/exact"][1])
    print(json.dumps({"native_cases":native_cases,"admitted_configs":admitted,
                      "frontier":archive_summary,"witnesses":routes,"enqueue_owner_control":owner},sort_keys=True))
if __name__=="__main__":main()
