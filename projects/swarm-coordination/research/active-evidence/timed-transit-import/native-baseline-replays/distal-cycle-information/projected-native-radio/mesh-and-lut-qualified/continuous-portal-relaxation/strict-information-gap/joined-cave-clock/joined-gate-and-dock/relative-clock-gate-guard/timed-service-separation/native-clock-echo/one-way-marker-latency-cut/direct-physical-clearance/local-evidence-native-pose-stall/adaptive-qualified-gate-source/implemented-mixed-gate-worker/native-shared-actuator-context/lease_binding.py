"""Two typed duty requests sharing one actual actuator lease."""
from dataclasses import dataclass
from typing import NamedTuple

class Lease(NamedTuple):
    key:str
    actor:int
    start:int
    end:int

@dataclass(frozen=True)
class Context:
    owner:int
    # Lease is an actuator-scoped live resource, independent of owner epoch.
    leases:tuple[Lease,...]

@dataclass(frozen=True)
class Content:
    # Fixed gate, mission and physical evidence version in this slice.
    body_clear:bool
    historical:Lease|None

def bind(context,content,key,actor,start,duration):
    assert duration>0
    if content.historical is not None:
        assert content.historical.key==key
        return ('historical',content.historical)
    if context.owner!=actor:return ('stale',None)
    if not content.body_clear:return ('physically-unqualified',None)
    end=start+duration-1
    if any(max(ll.start,start)<=min(ll.end,end) for ll in context.leases):
        return ('busy',None)
    return ('install',Lease(key,actor,start,end))
