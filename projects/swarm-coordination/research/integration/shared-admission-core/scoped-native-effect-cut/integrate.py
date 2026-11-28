from pathlib import Path

w=Path("gate/worker.py")
s=Path("gate/worker.baseline").read_text()
s=s.replace("import sqlite3,os","import sqlite3,os,subprocess")
start=s.index("        prior=State(")
stop=s.index("        if cut=='before':os._exit(51)",start)
s=s[:start]+'''        # This call executes under the database transaction enclosing
        # these reads and the owned single modeled gate effect.
        def classify(act,scope,value,room,service):
            return int(subprocess.check_output([
                os.environ['SCOPED_CUT_BIN'],act,
                *(str(int(bool(x))) for x in (scope,value,room,service))],
                text=True))
        if receipt is not None:
            # This protocol supports keyed exact replay. Read permission
            # is explicitly fixed for the two declared principals and
            # separate from permission to create another gate closure.
            response=classify('inspect',principal in (10,11),True,False,False)
            assert response==0
            outcome,origin,_=receipt
            assert origin<=t
        else:
            intent,duration=db.execute("SELECT nominal,span FROM Pending WHERE key=?",(key,)).fetchone()
            assert intent<=t
            intervals=db.execute("""
                SELECT i.start,i.finish
                FROM Installed i LEFT JOIN EffectAuthority a ON i.key=a.key
                WHERE (?=0 OR a.principal=?)
            """,(int(rule=='owner-only'),owner))
            last=t+duration-1
            room=not any(start<=last and t<=finish for start,finish in intervals)
            scope=declared==(principal,) and owner==principal
            response=classify('effect',scope,fact,room,True)
            if response==2:
                db.execute("INSERT OR IGNORE INTO Denied VALUES (?,?,?)",(key,principal,owner))
                db.execute("COMMIT")
                print("stale")
                raise SystemExit
            if response==4:
                db.execute("ROLLBACK")
                print("busy")
                raise SystemExit
            # The native gate protocol may record a negative decision
            # when evidence of clearance is missing; it must not close.
            assert response in (3,6)
            outcome='closed' if response==6 else 'blocked'
            events_at=db.execute("SELECT MAX(at) FROM Event").fetchone()[0]
            assert events_at is None or events_at<=t
            db.execute("INSERT INTO Receipt VALUES (?,?,?)",(key,t,outcome))
            db.execute("INSERT INTO Event VALUES (?,?,?)",(key,t,outcome))
            if response==6:
                db.execute("INSERT INTO Installed VALUES (?,?,?)",(key,t,t+duration-1))
                db.execute("INSERT INTO EffectAuthority VALUES (?,?,?)",(key,principal,owner))
'''+s[stop:]
s=s.replace("        from kernel import Context,Content,State,step\n","")
w.write_text(s)

p=Path("radio/checks.cpp")
r=Path("radio/checks.baseline").read_text()
r=r.replace('#include "parent.inc"','#include "parent.inc"\n#include "cut_contract.h"')
old='''        if(!bestDirectScope(p)||!dispatchReady())return false;
        return d.apply({"diagnostic","Aux",Radio::D,d.gen},cut,d.gen);'''
new='''        // This is a NEW native radio effect even though its content
        // is an old stored exact result. It cannot use inspect mode.
        const Request q{"diagnostic","Aux",Radio::D,d.gen};
        const Word* value=d.value(q);
        const bool room=value&&d.used(d.physical[q.subject],cut)+value->size()<=6&&
                               d.used(d.receive[q.dest],cut)+value->size()<=6;
        const auto profile=cut::Profile{cut::Act::effect,bestDirectScope(p),value!=nullptr,room,dispatchReady()};
        if(cut::check(profile)!=cut::enable)return false;
        return d.wire(q.subject,q.dest,*value,cut);'''
assert r.count(old)==1
p.write_text(r.replace(old,new))
