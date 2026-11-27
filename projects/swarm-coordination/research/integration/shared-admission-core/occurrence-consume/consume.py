"""Frozen restricted effect/use predicate. Inputs must come from checked adapters."""
from dataclasses import dataclass
from fractions import Fraction

@dataclass(frozen=True)
class Event:
    seq:int
    at:Fraction
    scope:str
    role:str
    parent:int|None
    value:str
    qualified:bool=True

@dataclass(frozen=True)
class Contract:
    scope:str
    roles:tuple
    wanted:int
    by:Fraction
    value:str

def first(events,law):
    """Find one timely effect of named origin along this allowed role chain."""
    seen={}
    cursor=None
    for e in events:
        if cursor and (e.seq<=cursor.seq or e.at<cursor.at):raise ValueError('noncausal input')
        if e.parent is not None and e.parent not in seen:raise ValueError('missing parent')
        seen[e.seq]=e
        cursor=e
    for z in seen.values():
        if z.role!=law.roles[-1] or z.at>law.by or z.value!=law.value:
            continue
        node=z
        ii=len(law.roles)-1
        while node.scope==law.scope and node.qualified and node.role==law.roles[ii]:
            if ii==0:
                if node.seq==law.wanted and node.parent is None:
                    return z.seq
                break
            if node.parent is None:break
            node=seen[node.parent]
            ii-=1
    return None
