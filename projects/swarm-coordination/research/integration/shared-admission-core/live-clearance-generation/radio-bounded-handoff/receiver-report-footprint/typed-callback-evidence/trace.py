"""Offline source to normalized prefix, never a control oracle."""
from dataclasses import dataclass
from fractions import Fraction
from collections import defaultdict

@dataclass(frozen=True)
class Attempt:
    time: Fraction
    sender: str
    recipient: str
    offered: int
    charged: int
    radio_admitted: bool
    proof: int

@dataclass(frozen=True)
class Callback:
    time: Fraction
    sender: str
    endpoint: str
    size: int
    body: str
    attempt: int
    proof: int

def samples(s):
    return tuple((Fraction(x),int(y)) for x,y in (z.split(':') for z in s.split(','))) if s!='-' else ()

def alive(rows,t):
    return tuple((u,n) for u,n in rows if t-u<=1)

def parse(raw,cap,bind):
    ledgers=defaultdict(tuple)
    attempts={}; callbacks={}
    pending=None
    count=0
    at=Fraction(0)
    for line in raw:
        kind,k,t,*rest=line.split()
        k=int(k);t=Fraction(t)
        if k!=count+1 or t<at:raise ValueError('order/proof')
        at=t;count=k
        if kind=='attempt':
            if pending is not None: raise ValueError('missing accepted callback')
            s,r,n,ba,bb,pa,pb,current=rest
            n=int(n);before=(samples(ba),samples(bb));after=(samples(pa),samples(pb))
            order=((s,'tx'),(r,'rx'))
            if tuple(ledgers[x] for x in order)!=before:raise ValueError('scope/history')
            x,y=before;a,b=after
            x0,y0=alive(x,t),alive(y,t)
            tx_cost=n if sum(m for _,m in x0)+n<=cap else 0
            if a!=x0+(((t,n),) if tx_cost else ()):raise ValueError('TX mutation')
            if current not in ('0','1') or n<=0:raise ValueError('attempt domain')
            reached=(current=='1')
            if reached and (not tx_cost or sum(m for _,m in y0)+n>cap or b!=y0+((t,n),)):
                raise ValueError('RX admission')
            if not reached and b not in (y,y0):raise ValueError('RX mutation without delivery')
            if not tx_cost and b!=y:raise ValueError('RX called without TX')
            for name,data in zip(order,after):ledgers[name]=data
            attempts[k]=Attempt(t,s,r,n,tx_cost,reached,k)
            pending=k if reached else None
        elif kind=='callback':
            s,ep,n,body=rest
            n=int(n)
            if pending is None:raise ValueError('unbacked callback')
            a=attempts[pending]
            if (t,s,bind.get(ep),n)!=(a.time,a.sender,a.recipient,a.offered) or len(body)!=n:
                raise ValueError('callback identity')
            callbacks[k]=Callback(t,s,ep,n,body,pending,k)
            pending=None
        else:raise ValueError('event kind')
    if pending is not None:raise ValueError('missing final callback')
    return attempts,callbacks

def typed_consume(callbacks,attempts,old_intent,authority,due=Fraction(5,4)):
    # Authority belongs to the simulator station; radio delivery alone
    # does not decide whether a live intent may be reused.
    active={"P":"Base:7","Q":"alt:7"}
    body=old_intent+('r'*(173-len(old_intent)))
    entries=[]
    for k,c in callbacks.items():
        if c.endpoint!=active.get(c.sender) or c.body!=body or c.time>due:
            continue
        if not authority:continue
        if attempts[c.attempt].charged!=173:raise ValueError('missing old send debit')
        entries.append((k,c.attempt))
    if len(entries)>1:raise ValueError('fixture publisher expected one receipt')
    return entries[0] if entries else None
