"""Discrete serialized reference wrapper for one old duty after physical reentry."""
from core import Row, Use, Event, check

CLEAR=('source','fresh-named-clearance')
PERMIT=('auth','qualified-arrival','owed')
BACK=('role','backup-Q')

def pick_core(t,cap,need,has_permit,clear,backup,radio):
    """Select only from actual local row and fact reads at this cut."""
    facts={f for f,ok in [(CLEAR,clear),(PERMIT,has_permit),(BACK,backup)] if ok}
    # Active sums are sufficient for this one consuming instant only.
    # These are not re-dated entries retained for later ticks.
    p,q,rx=radio
    earlier=tuple(Event(t,k,uses=(Use(key,amount,cap,0),)) for k,(key,amount) in
                  enumerate(((('TX','P'),p),(('TX','Q'),q),(('RX','Base'),rx))) if amount)
    for src in ('P','Q'):
        req=(CLEAR,PERMIT,BACK) if src=='Q' else (CLEAR,PERMIT)
        event=Event(t,8,need=frozenset(req),
             uses=(Use(('TX',src),need,cap,0),Use(('RX','Base'),need,cap,0)),paid=('owed',))
        row=Row((),frozenset(facts),earlier,{src:(event,)})
        if check(row,src,t,{'owed':t}):
            return src
    return None
