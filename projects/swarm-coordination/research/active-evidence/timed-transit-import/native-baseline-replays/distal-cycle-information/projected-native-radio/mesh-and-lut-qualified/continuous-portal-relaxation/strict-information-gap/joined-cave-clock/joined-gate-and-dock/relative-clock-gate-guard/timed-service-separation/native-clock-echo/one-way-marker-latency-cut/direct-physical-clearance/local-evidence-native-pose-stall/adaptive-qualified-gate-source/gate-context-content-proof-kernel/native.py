"""SQLite-owned simulator gate; the plant's effect is not a physical relay."""
from pathlib import Path
from sys import argv
import sqlite3,os
from contextlib import closing
file,action,*args=argv[1:]
with closing(sqlite3.connect(file,isolation_level=None)) as db:
    db.execute('PRAGMA synchronous=FULL')
    db.execute('BEGIN IMMEDIATE')
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
    assert action=='apply' and rule in ('effect','clearance','cached')
    row=db.execute('SELECT at,decision FROM Receipt WHERE key=?',(key,)).fetchone()
    if row:
        assert row[0]<=clock
        decision=row[1]
    else:
        intent,duration=db.execute('SELECT nominal,span FROM Pending WHERE key=?',(key,)).fetchone()
        assert 0<=intent<=clock
        events_at=db.execute('SELECT MAX(at) FROM Event').fetchone()[0]
        assert events_at is None or events_at<=clock
        if rule in ('clearance','cached'):
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
            if rule in ('clearance','cached'):
                db.execute("INSERT INTO EffectAuthority VALUES (?,?,?)",(key,actor,holder))
    if cut=='before':
        os._exit(51)  # SQLite must recover the interrupted transaction.
    db.execute('COMMIT')
    if cut=='after':
        os._exit(52)  # No reply; replacement returns the exact prior result.
    assert cut=='reply'
    print(decision)
