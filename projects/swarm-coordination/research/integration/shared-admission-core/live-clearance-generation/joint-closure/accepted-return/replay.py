"""Normal station restart and cooperative use of a shared modeled bay."""
from collections import defaultdict
from itertools import product
from pathlib import Path
import json,os,sqlite3,subprocess,sys,tempfile

ROOT=Path(sys.argv[1])
sys.path.insert(0,str(ROOT))
import journal

def accept_worker(file,stage):
    d=sqlite3.connect(file,isolation_level=None)
    d.execute("pragma synchronous=full")
    d.execute("begin immediate")
    assert d.execute("select sealed from epoch where id=7").fetchone()==(0,)
    d.execute("insert into authority values(7,'old-return','accepted')")
    if stage=="durable":d.commit()
    os._exit(77)

def make():
    n=journal.n; A=n.Action
    source=journal.iso.make(n,True)
    c,s=source.agents
    c.dir=n.Direction.RIGHT
    s.x,s.y,s.dir=1,3,n.Direction.RIGHT
    source._recalc_grid()
    for a in (A.TOGGLE_LOAD,A.FORWARD,A.RIGHT,A.RIGHT):
        n.step(source,[a.value,A.NOOP.value])
    visitor=n.Agent(2,1,n.Direction.UP,0)
    source.agents.append(visitor);source.n_agents=3
    source._recalc_grid()
    assert (c.x,c.y)==(3,0) and c.dir==n.Direction.LEFT
    return source

def compare(old,drop,backup,cap,arm):
    qualified=not drop or backup
    once=qualified and (arm=="eager" or arm=="guard" and not old)
    early=once and not old
    blocked=arm=="occupancy-only"
    if blocked:return (6,not old)
    if early:return (6,True)
    return (11 if once and cap<6 else 9,True)

def main():
    n=journal.n; A=n.Action
    with subprocess.Popen([str(Path(sys.argv[2]).resolve())],stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE,text=True,bufsize=1) as wire:
      def ask(*args): 
        wire.stdin.write(" ".join(map(str,args))+"\n");wire.stdin.flush()
        return wire.stdout.readline().strip()
      def run(loc,stage,drop,backup,cap,arm):
        assert ask("reset",cap)=="ok"
        g=make(); c,s,v=g.agents
        d=sqlite3.connect(loc,isolation_level=None)
        d.executescript("""pragma journal_mode=wal; pragma synchronous=full;
           create table epoch(id integer primary key,sealed int);
           insert into epoch values(7,0);
           create table authority(epoch int,key text primary key,state text);
        """)
        result=subprocess.run([sys.executable,"-B",__file__,str(ROOT),"worker",loc,stage])
        assert result.returncode==77
        # The replacement is given the lock to seal the retired source
        # epoch. Old accepted entries survive this; it only forbids new ones.
        d.execute("begin immediate")
        d.execute("update epoch set sealed=1 where id=7")
        d.commit()
        def state():
            assert d.execute("select sealed from epoch where id=7").fetchone()==(1,)
            x=d.execute("select state from authority where epoch=7 and key='old-return'").fetchone()
            return x[0] if x else "absent"
        old=state()=="accepted";assert old==(stage=="durable")
        public={"restart":"reset","old_pose":[c.x,c.y],"bay_empty":not any((x.x,x.y)==(2,0) for x in g.agents)}
        assert public=={"restart":"reset","old_pose":[3,0],"bay_empty":True}
        transmissions=[]
        def send(t,src,dest,b,link=True):
            msg,used=ask("send",t,src,dest,b,int(link)).split()
            assert msg in ("-",b) and int(used) in (0,len(b))
            transmissions.append([t,src,dest,b,msg,int(used)])
            return msg
        def step(x=A.NOOP,y=A.NOOP,z=A.NOOP):
            n.step(g,[x.value,y.value,z.value])
        # Q is installed via one real link; the separate second fault
        # affects this proof route only after its installation.
        assert send(4,"Side","setup","up")=="up"
        payload="n7!" if state()=="absent" else "l7!"
        announce=arm=="eager" or (arm=="guard" and payload=="n7!")
        known="-"
        if announce:known=send(5,"Q","proof",payload,not drop)
        # Unrelated native work on the same timeline while Q fails.
        assert ask("side",5)=="1";step(y=A.FORWARD)
        assert (s.x,s.y)==(2,3)
        if announce and known=="-" and backup:
            known=send(6,"X","proof",payload)
        early=known=="n7!" or arm=="occupancy-only"
        entry=None
        if early:
            step(z=A.FORWARD)
            assert (v.x,v.y)==(2,0)
            entry=6
        if state()=="accepted":
            step(x=A.FORWARD)
            if (c.x,c.y)==(2,0):
                step(x=A.FORWARD)
                if (c.x,c.y)==(2,0):
                    # The fixture permits a safe return to the known
                    # starting cell if forward clearance is not available.
                    step(x=A.LEFT);step(x=A.LEFT);step(x=A.FORWARD)
                assert (c.x,c.y)!=(2,0)
                d.execute("update authority set state='settled' where key='old-return'")
        old_position=[c.x,c.y]
        success=state()!="accepted"
        if entry is None:
            assert success and not any((x.x,x.y)==(2,0) for x in g.agents)
            # Actual old movement/clearance happened before emitting this.
            proof=send(9,"Base","proof","d7!")
            entry=9
            if proof=="-":
                proof=send(11,"X","proof","d7!");entry=11
            assert proof=="d7!"
            step(z=A.FORWARD)
            assert (v.x,v.y)==(2,0)
        assert (entry,success)==compare(old,drop,backup,cap,arm),(
            stage,drop,backup,cap,arm,entry,success,transmissions)
        d.close()
        return dict(public=public,early=known,entry=entry,old_paid=success,old_position=old_position,side_tick=5,wire=transmissions)
      rows=[]
      for case in product(("rolled","durable"),(False,True),(False,True),(5,6),
                          ("guard","eager","safe-wait","occupancy-only")):
        with tempfile.TemporaryDirectory() as d:
          rows.append([*case,run(str(Path(d)/"owner.db"),*case)])
      arms={}
      for arm in ("guard","eager","safe-wait","occupancy-only"):
        a=[r[-1] for r in rows if r[4]==arm]
        arms[arm]=dict(n=len(a),old_paid=sum(x["old_paid"] for x in a),
                 by9=sum(x["entry"]<=9 and x["old_paid"] for x in a),
                 early=sum(x["entry"]==6 and x["old_paid"] for x in a))
      assert arms["guard"]==dict(n=16,old_paid=16,by9=16,early=6)
      wire.stdin.close();assert wire.wait()==0
    print(json.dumps(dict(arms=arms,witness=[r for r in rows if r[1:4]==[True,True,5]]),
                     sort_keys=True,indent=2))

if __name__=="__main__":
    if sys.argv[2]=="worker":accept_worker(sys.argv[3],sys.argv[4])
    else:main()
