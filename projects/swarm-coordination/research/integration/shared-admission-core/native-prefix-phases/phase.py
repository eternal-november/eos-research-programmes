"""Refinement of a native prefix into the unchanged all-pay admission core."""
from core import Event, Use

RELEASE=('qualified-departure','carrier-P','bay-2-0')
DROPPED=('load-down','carrier-P','bay-2-0')
BACKUP=('qualified-use','Q','old-report')
SIDE_R='separate-radio'
SIDE_W='separate-motion'
OLD='owed-report'

def radio_history(cap,seed,tx,rx,delivered,side,collapse=False):
    if (rx>tx or bool(rx)!=bool(delivered) or not side
            or any(x>cap or x<0 for x in (seed,tx,rx)) or seed+rx>cap):
        raise ValueError('ill-typed selected native observation')
    out=[]
    if seed:
        out.append(Event(0,0,uses=(Use(('rx','R0'),seed,cap,4),)))
    # The source returns actual prefix debits, not "did a message arrive?".
    if tx and (delivered or not collapse):
        out.append(Event(0,1,uses=(Use(('tx','P'),tx,cap,4),)))
    if rx:
        out.append(Event(0,2,uses=(Use(('rx','R0'),rx,cap,4),)))
    out.append(Event(2,10,uses=(Use(('tx','Side'),1,cap,4),Use(('rx','Far'),1,cap,4)),
                     paid=(SIDE_R,)))
    return tuple(out)

def warehouse_history(samples,collapse=False):
    facts=set()
    events=[]
    for t,x,y,loaded,side_at in samples:
        after={DROPPED} if not loaded else set()
        if not loaded and ((x,y)==(3,0) or collapse):
            after.add(RELEASE)
        if after!=facts:
            events.append(Event(t,10,add=frozenset(after-facts),drop=frozenset(facts-after)))
        if t==4:
            if side_at!=(2,3):
                raise ValueError('separate motion did not reach its actual cell')
            events.append(Event(t,11,paid=(SIDE_W,)))
        facts=after
    return tuple(events)

def options(cap,a,alias):
    out={}
    for name,src,t in [('early','P',4),('backup','Q',4),('late','P',6)]:
        need=frozenset((RELEASE,BACKUP)) if src=='Q' else frozenset((RELEASE,))
        out[name]=(Event(t,20,need=need,
                  uses=(Use(('tx',src),a,cap,4),Use(('rx','R0' if alias else 'R1'),a,cap,4)),
                  paid=(OLD,)),)
    return out
