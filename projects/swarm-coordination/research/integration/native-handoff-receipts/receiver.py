from dataclasses import dataclass
from typing import Hashable

@dataclass(frozen=True)
class Cut:
    before: tuple
    applied: tuple
    service: tuple
    pending: frozenset

def confirm(x, port, old, new, debt):
    if old==new: return False
    before={a for a,p in x.before if p==port}
    applied={a for a,p in x.applied if p==port}
    return (before=={old} and applied=={new} and
            (new,port) in x.service and (old,debt) in x.pending)
