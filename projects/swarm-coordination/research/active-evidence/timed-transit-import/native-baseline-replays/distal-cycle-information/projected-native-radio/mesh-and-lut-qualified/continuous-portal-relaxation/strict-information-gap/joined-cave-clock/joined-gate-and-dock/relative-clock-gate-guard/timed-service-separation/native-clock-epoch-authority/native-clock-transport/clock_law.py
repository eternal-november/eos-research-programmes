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

def transported(db):
    era,=db.execute("SELECT era FROM ActiveClock").fetchone()
    current=fit(db.execute("SELECT s,g,r FROM Echo WHERE era=? ORDER BY s",(era,)).fetchall())
    # The scoped fixture permits one source era, one durable, qualified
    # transport witness, and at most one qualified active authority.
    rel=db.execute("SELECT old,low,high FROM ClockBridge WHERE new=?",(era,)).fetchall()
    if not rel:return current
    [(src,l,u)]=rel
    assert src!=era and l<=u
    previous=fit(db.execute("SELECT s,g,r FROM Echo WHERE era=? ORDER BY s",(src,)).fetchall())
    out=Bounds(max(current.low,previous.low+l),min(current.high,previous.high+u))
    assert out.low<=out.high
    return out
