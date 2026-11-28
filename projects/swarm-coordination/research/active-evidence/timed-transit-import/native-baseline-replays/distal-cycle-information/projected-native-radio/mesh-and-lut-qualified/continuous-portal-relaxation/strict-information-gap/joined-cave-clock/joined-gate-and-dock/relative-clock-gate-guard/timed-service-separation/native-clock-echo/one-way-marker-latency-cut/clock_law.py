"""Gate timestamps under a fixed offset, with zero turnaround in a sync fixture."""
from typing import NamedTuple
class Bounds(NamedTuple):
    low:int
    high:int

def fit(samples):
    # master send, gate receive/echo, master receive
    a=max(g-b for a,g,b in samples)
    b=min(g-a for a,g,b in samples)
    assert a<=b
    return Bounds(a,b)

def source(kind,phase,held_end,record):
    # The simulator owns the physical times and is NOT an input to the
    # admission calculation. Only the echo records and gate stamp cross it.
    clock=held_end-49995 if not phase else held_end+50005
    offset=(50000,-50000)[phase]
    assert clock+offset==held_end+5
    def echo(a,dx,dy):
        assert 0<=dx and 0<=dy
        return a,a+dx+offset,a+dx+dy
    w=echo(50_000_000,50000-offset,50000+offset)
    n=echo(60_000_000,5000,15000)
    rr={'wide':[w],'narrow':[n],'cumulative':[w,n]}[kind]
    assert all(0<a<=b<clock for a,g,b in rr)
    assert fit(rr).low<=offset<=fit(rr).high
    # Record only real timestamps available to the consuming actor.
    record(rr)
    return clock,clock+offset

def deny(holds,span,stamp,bounds):
    lo,hi=stamp-bounds.high,stamp-bounds.low+span-1
    return any(not(hi<a or b<lo) for a,b in holds)

def earliest_after(held_end,stamp,bounds):
    # This fixture only attempts end-side release, with no future holds.
    # For a fixed offset, waiting d on the gate clock waits d in the
    # motion clock too. Inclusive old occupancy makes the +1 material.
    return max(0,held_end+1+bounds.high-stamp)

def marker_bounds(db):
    old=fit(db.execute("SELECT s,g,r FROM Echo ORDER BY s").fetchall())
    A,g,latest,era=db.execute("SELECT anchor,g,latest,era FROM Marker").fetchone()
    assert era==7
    out=Bounds(max(old.low,g-A-latest) if latest is not None else old.low,
                min(old.high,g-A))
    assert out.low<=out.high
    return out
