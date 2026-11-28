"""SQLite-owned simulator gate; the plant's effect is not a physical relay."""
from pathlib import Path
from sys import argv
import sqlite3,os
from contextlib import closing
file,action,*args=argv[1:]
with closing(sqlite3.connect(file,isolation_level=None)) as db:
    db.execute('PRAGMA synchronous=FULL')
    db.execute('BEGIN IMMEDIATE')
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
    assert action=='apply' and rule in ('effect','stamp','bounded')
    row=db.execute('SELECT at,decision FROM Receipt WHERE key=?',(key,)).fetchone()
    if row:
        assert row[0]<=clock
        decision=row[1]
    else:
        intent,duration=db.execute('SELECT nominal,span FROM Pending WHERE key=?',(key,)).fetchone()
        assert 0<=intent<=clock
        events_at=db.execute('SELECT MAX(at) FROM Event').fetchone()[0]
        assert events_at is None or events_at<=clock
        if rule=='effect':
            conflict=db.execute("""
              SELECT EXISTS (SELECT 1 FROM Hold WHERE start <= ? AND ? <= finish)
            """,(clock+duration-1,clock)).fetchone()[0]
        else:
            # Use only real external clock evidence and the unchanged
            # occupancy authority. The absolute simulator time is
            # not supplied to this guard or used in its decision.
            from clock_law import fit,deny,Bounds
            stamp,=map(int,stamp_)
            echo=db.execute("SELECT s,g,r FROM Echo ORDER BY s").fetchall()
            assert echo
            limits=fit(echo) if rule=='bounded' else Bounds(0,0)
            conflict=deny(db.execute("SELECT start,finish FROM Hold").fetchall(),duration,stamp,limits)
        decision='blocked' if conflict else 'closed'
        db.execute('INSERT INTO Receipt VALUES (?,?,?)',(key,clock,decision))
        db.execute('INSERT INTO Event VALUES (?,?,?)',(key,clock,decision))
        if decision=='closed':
            db.execute('INSERT INTO Installed VALUES (?,?,?)',(key,clock,clock+duration-1))
    if cut=='before':
        os._exit(51)  # SQLite must recover the interrupted transaction.
    db.execute('COMMIT')
    if cut=='after':
        os._exit(52)  # No reply; replacement returns the exact prior result.
    assert cut=='reply'
    print(decision)
