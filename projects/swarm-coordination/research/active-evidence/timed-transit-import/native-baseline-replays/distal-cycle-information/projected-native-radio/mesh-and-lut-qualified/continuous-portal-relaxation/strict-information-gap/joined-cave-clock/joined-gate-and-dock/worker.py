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
    key,clock,rule,cut=args
    clock=int(clock)
    assert action=='apply' and rule in ('issued','intent','volatile','effect')
    row=db.execute('SELECT at,decision FROM Receipt WHERE key=?',(key,)).fetchone()
    if row:
        assert row[0]<=clock
        decision=row[1]
    else:
        intent,duration=db.execute('SELECT nominal,span FROM Pending WHERE key=?',(key,)).fetchone()
        assert 0<=intent<=clock
        events_at=db.execute('SELECT MAX(at) FROM Event').fetchone()[0]
        assert events_at is None or events_at<=clock
        eval_clock=clock if rule=='effect' else intent
        # Closed integer intervals. With a new owner, the volatile
        # design has lost in-memory protection. 'issued' performed
        # the reservation test only when creating its pending request.
        conflict=rule in ('intent','effect') and db.execute('''
               SELECT EXISTS (SELECT 1 FROM Hold WHERE start <= ? AND ? <= finish)
        ''',(eval_clock+duration-1,eval_clock)).fetchone()[0]
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
