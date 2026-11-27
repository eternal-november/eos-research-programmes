"""Source-backed robust cut with transport-charged evidence."""
import json,sqlite3,subprocess,tempfile
from itertools import product
from pathlib import Path
from core import Row, Event, Use, admitted
from run_core import A,B
root=Path(__file__).resolve().parent
KINDS=("early","silent","hidden","visible")
M={"B":(("R",8),),"B_":(("R",9),),"QB":(("Q",8),("R",8)),
   "BQ":(("R",8),("Q",8)),"Q_B":(("Q",8),("R",9)),
   "B_Q":(("R",8),("Q",9)),"_QB":(("Q",9),("R",9)),
   "_BQ":(("R",9),("Q",9))}
# Option ordering prefers fewer transmissions and earlier B when feasible.
RX=("Scout","rx")

def model(kind,medium,t,widen,onlyB=False):
    early=kind in ("early","silent")
    cert=kind=="early" and medium!="none"
    absent=not early and medium!="none"
    known=kind=="visible"
    obs=(int(known),int(cert),int(absent))
    prefix=[]
    history=[]
    if not early:
        prefix.append(Event(4,0,uses=(Use(RX,2,4,4),),paid=() if onlyB else ("A",)))
        history.append((4,2))
    if medium=="radio" and (cert or absent):
        prefix.append(Event(t,1,uses=(Use(RX,1,8,4),)))
        history.append((t,1))
    opts={}
    expected={}
    for name,seq in M.items():
        at={"A":4 if not early else -1,"B":-1}
        active=history[:]
        future=[]
        for idx,(sender,tick) in enumerate(seq):
            size,cap,d=(2,4,"A") if sender=="Q" else (3,5+widen,"B")
            good=sum(n for s,n in active if (tick-4)<=s)<=cap-size
            uses=(Use((sender,"tx"),size,cap,4),)
            pay=()
            if good:
                active.append((tick,size))
                uses+=(Use(RX,size,cap,4),)
                if at[d]<0:
                    at[d]=tick
                    pay=() if onlyB and d=="A" else (d,)
            future.append(Event(tick,idx,uses=uses,paid=pay))
        opts[name]=tuple(future)
        expected[name]={**at,"received":sum(n for _,n in active),"side":1}
    return Row(((7,"Scout",obs),),frozenset(),tuple(prefix),opts),obs,expected

def live(kind,medium,t,widen,pick):
    with subprocess.Popen([str(root/"score"),"two","exact","exact"],stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE,text=True) as s:
        proof=json.loads(s.stdout.readline())
        assert (proof["A"],proof["B"],proof["A_key"],proof["B_key"])==(1,1,A,B)
        with tempfile.TemporaryDirectory() as p:
            db=Path(p)/"archive"
            with sqlite3.connect(db) as d:
                d.execute("create table exact (k text primary key)")
                d.executemany("insert into exact values (?)",((A,),(B,)))
            with sqlite3.connect(db) as d:
                codes="".join(label for label,k in (("A",A),("B",B))
                              if d.execute("select 1 from exact where k=?",(k,)).fetchone())
        with subprocess.Popen([str(root/"charged"),kind,medium,str(t),str(widen)],
                stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as r:
            r.stdin.write(codes+"\n");r.stdin.flush()
            assert json.loads(r.stdout.readline())=={"stage":3}
            after,_=s.communicate("next\n",timeout=5)
            assert s.returncode==0 and json.loads(after)=={"closed":1,"independent":1}
            r.stdin.write("closed\n");r.stdin.flush()
            frame=json.loads(r.stdout.readline())
            local=tuple(frame[k] for k in ("known","cert","absence"))
            # Do not pass evaluator's live rx count or hidden schedule to policy.
            option=pick(local)
            reply,_=r.communicate(option+"\n",timeout=5)
            assert r.returncode==0
            return local,option,json.loads(reply)

def main():
    out={}; runs=0
    for medium,t,w,deadline in product(("radio","local","none"),range(4,7),(0,1),(8,9)):
        params=medium,t,w
        worlds={k:model(k,*params) for k in KINDS}
        full=admitted([m[0] for m in worlds.values()],"Scout",7,{"A":deadline,"B":deadline},M)
        fallback=admitted([model(k,*params,onlyB=True)[0] for k in KINDS],"Scout",7,{"B":deadline},M)
        def acceptable(g,keys):
            return all(0<=g[k]<=deadline for k in keys)
        for view in full:
            cell=[v[2] for v in worlds.values() if v[1]==view[0][1]]
            for opts,check in [(full,("A","B")),(fallback,("B",))]:
                direct=tuple(a for a in M if all(acceptable(c[a],check) for c in cell))
                assert opts[view]==direct,(params,deadline,view,check,opts[view],direct)
        for k,(_,obs,direct) in worlds.items():
            for a in M:
                local,_,g=live(k,*params,lambda _:a)
                assert local==obs and g==direct[a],(k,params,a,g,direct[a],obs)
                runs+=1
            def choose(local):
                return next(iter(full[((7,local),)] or fallback[((7,local),)]),"B")
            local,option,result=live(k,*params,choose)
            runs+=1
            assert local==obs and result==direct[option]
            out[f"{medium}/{t}/{w}/{deadline}/{k}"]={
                "obs":obs, "full":full[((7,obs),)],"fallback":fallback[((7,obs),)],
                "choose":option,"result":result}
    def certain(t,w,d,a):
        return a in out[f"radio/{t}/{w}/{d}/early"]["full"]
    assert not out["radio/4/0/8/early"]["full"]
    assert certain(4,0,9,"Q_B") and not certain(4,0,9,"B_Q")
    assert not out["radio/5/0/9/early"]["full"]
    assert certain(6,1,8,"QB") and not certain(6,1,8,"BQ")
    assert "QB" in out["local/4/0/8/early"]["full"]
    assert not out["none/4/0/8/early"]["full"]
    assert not out["radio/4/0/8/hidden"]["fallback"]
    # Same received E by the cut, with no trusted receive tick in the interface.
    # Pool source histories for all admissible receive times, not just the favorable t=4.
    outs={}
    for ticks,deadline,w in product(((4,), (5,), (4,5), (4,5,6)), (8,9), (0,1)):
        worlds=[model(k,"radio",t,w) for k,t in product(KINDS,ticks)]
        ch=admitted([m[0] for m in worlds],"Scout",7,{"A":8,"B":deadline},M)
        key=((7,(0,1,0)),)
        opts=ch[key]
        matches=tuple(a for a in M if all(0<=m[2][a]["A"]<=8 and
                        0<=m[2][a]["B"]<=deadline for m in worlds if m[1]==(0,1,0)))
        assert matches==opts
        outs[f"{ticks}/{deadline}/{w}"]=opts
        if w==0:
            assert bool(opts)==(deadline==9 and ticks==(4,))
            if opts: assert opts==("Q_B",)
        else: assert "QB" in opts
    print(json.dumps({"native_cases":runs,"results":out,"unknown_receive_tick":outs},sort_keys=True))
if __name__=="__main__":main()
