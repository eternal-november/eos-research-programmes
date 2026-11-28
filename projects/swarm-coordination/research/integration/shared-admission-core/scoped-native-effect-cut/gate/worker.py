"""SQLite-owned simulator gate; the plant's effect is not a physical relay."""
from pathlib import Path
from sys import argv
import sqlite3,os,subprocess
from contextlib import closing
file,action,*args=argv[1:]
with closing(sqlite3.connect(file,isolation_level=None)) as db:
    db.execute('PRAGMA synchronous=FULL')
    db.execute('BEGIN IMMEDIATE')
    if action=='apply' and args[2] in ('clearance','owner-only'):
        # The native store adapter reads layers separately. Both owner
        # and the effect/log settle state are within one serialization cut.
        key,at,rule,cut,actor=args
        t=int(at);principal=int(actor)
        assert key in ('Q','V') and principal in (10,11)
        declared=db.execute("SELECT principal FROM ActionScope WHERE key=?",(key,)).fetchone()
        assert declared in ((10,),(11,))
        owner,=db.execute("SELECT holder FROM Owner").fetchone()
        gate,era=db.execute("SELECT gate,era FROM Authority").fetchone()
        row=db.execute("SELECT at,decision FROM Receipt WHERE key=?",(key,)).fetchone()
        q=db.execute("SELECT principal FROM EffectAuthority WHERE key=?",(key,)).fetchone()
        receipt=None if row is None else (row[1],row[0],0 if q is None else q[0])
        assert (q is not None)==(receipt is not None and receipt[0]=='closed')
        fact=0
        for b, in db.execute("SELECT source FROM PhysicalSource WHERE gate=? AND era=? AND mission='return'",(gate,era)):
            assert b in (1,2)
            fact|=b
        # This call executes under the database transaction enclosing
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
        if cut=='before':os._exit(51)
        db.execute("COMMIT")
        if cut=='after':os._exit(52)
        assert cut=='reply'
        print(outcome)
        raise SystemExit
    if action=='transfer':
        mid,prior,next_,at=args
        old=int(prior);new=int(next_);t=int(at)
        prior_event=db.execute("SELECT prior,next,at FROM AuthChange WHERE key=?",(mid,)).fetchone()
        if prior_event:
            assert prior_event==(old,new,t)
            db.execute("COMMIT")
            print("transferred")
            raise SystemExit
        holder,=db.execute("SELECT holder FROM Owner").fetchone()
        assert holder==old and (old,new) in ((10,11),(10,0))
        # 0 is a withdrawal without preconsent for a successor.
        db.execute("UPDATE Owner SET holder=?",(new,))
        db.execute("INSERT INTO AuthChange VALUES (?,?,?,?)",(mid,old,new,t))
        db.execute("COMMIT")
        os._exit(44)
    if action=='issue':
        # This is a request witness, not an actual actuator effect.
        key,intent,duration=args
        intent,duration=int(intent),int(duration)
        assert 0<duration
        # Actual request-side precheck in every arm. It is prospective:
        # only the nominal coordinates are available before release.
        assert not db.execute("""
               SELECT EXISTS (SELECT 1 FROM Hold WHERE start <= ? AND ? <= finish)
        """,(intent+duration-1,intent)).fetchone()[0]
        db.execute('INSERT INTO Pending VALUES (?,?,?)' ,(key,intent,duration))
        db.execute('COMMIT')
        # Reproduce producer loss after durable enqueue before local reply.
        os._exit(43)
    key,clock,rule,cut,*stamp_=args
    clock=int(clock)
    assert action=='apply' and rule in ('effect','cached')
    row=db.execute('SELECT at,decision FROM Receipt WHERE key=?',(key,)).fetchone()
    if row:
        assert row[0]<=clock
        decision=row[1]
    else:
        intent,duration=db.execute('SELECT nominal,span FROM Pending WHERE key=?',(key,)).fetchone()
        assert 0<=intent<=clock
        events_at=db.execute('SELECT MAX(at) FROM Event').fetchone()[0]
        assert events_at is None or events_at<=clock
        if rule=='cached':
            actor,=map(int,stamp_)
            holder,=db.execute("SELECT holder FROM Owner").fetchone()
            assert actor in (10,11)
            recorded=db.execute("SELECT old_owner FROM QueuedOwner WHERE key=?",(key,)).fetchone()
            assert recorded==(10,)
            if actor!=(recorded[0] if rule=='cached' else holder):
                # An invalid principal has no power to settle the stable
                # obligation key. This is an attempt, not an effect record.
                db.execute("INSERT OR IGNORE INTO Denied VALUES (?,?,?)",(key,actor,holder))
                db.execute('COMMIT')
                print('stale')
                raise SystemExit
        if rule=='effect':
            conflict=db.execute("""
              SELECT EXISTS (SELECT 1 FROM Hold WHERE start <= ? AND ? <= finish)
            """,(clock+duration-1,clock)).fetchone()[0]
        else:
            # This qualified permission is for the full body of the
            # only active return mission, not a timestamp translation.
            site,era=db.execute("SELECT gate,era FROM Authority").fetchone()
            conflict=not db.execute("""SELECT EXISTS
              (SELECT 1 FROM ExitReceipt WHERE gate=? AND era=? AND mission='return')
            """,(site,era)).fetchone()[0]
        decision='blocked' if conflict else 'closed'
        db.execute('INSERT INTO Receipt VALUES (?,?,?)',(key,clock,decision))
        db.execute('INSERT INTO Event VALUES (?,?,?)',(key,clock,decision))
        if decision=='closed':
            db.execute('INSERT INTO Installed VALUES (?,?,?)',(key,clock,clock+duration-1))
            if rule=='cached':
                db.execute("INSERT INTO EffectAuthority VALUES (?,?,?)",(key,actor,holder))
    if cut=='before':
        os._exit(51)  # SQLite must recover the interrupted transaction.
    db.execute('COMMIT')
    if cut=='after':
        os._exit(52)  # No reply; replacement returns the exact prior result.
    assert cut=='reply'
    print(decision)
