"""Common live-issue kernel. Availability is not qualification."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Boundary:
    duty:str
    effect:str
    site:str
    arbiter:str
    epoch:int
    cut:int
    last:int
    old:frozenset
    new:frozenset

@dataclass(frozen=True)
class Receipt:
    kind:str
    duty:str
    effect:str
    site:str
    arbiter:str
    epoch:int
    sampled:int
    arrives:int
    until:int
    writers:frozenset=frozenset()
    value:int=-1

def qualified(r,b,last):
    return ((r.duty,r.effect,r.site,r.arbiter,r.epoch)==(b.duty,b.effect,b.site,b.arbiter,b.epoch)
        and r.sampled<=r.arrives<=b.cut<=last<=r.until)

def pick(b, entries):
    """Choose before issue; the realized adapter enforces any admitted mode.

    Terminal read fallback needs all old writers fenced THROUGH effect.
    A shared guard can allow blind attempts only if ALL possible writers
    have the same effect-local semantics through the end of interference.
    """
    entries=tuple(entries)
    if any(r.kind=='interlock' and qualified(r,b,b.last)
            and b.old|b.new <= r.writers for r in entries):
        return 'interlocked'
    if not any(r.kind=='fence' and qualified(r,b,b.last)
            and b.old <= r.writers for r in entries):
        return 'hold'
    # A read must be taken after an already effective terminal fence.
    fences=[r for r in entries if r.kind=='fence' and qualified(r,b,b.last)
                                   and b.old <= r.writers]
    vals={r.value for r in entries if r.kind=='effect-read'
          and qualified(r,b,b.cut) and r.value in (0,1)
          and any(f.sampled<=r.sampled for f in fences)}
    if vals=={0}:return 'issue'
    if vals=={1}:return 'avoid-repeat'
    return 'hold'

def direct(b,rs):
    """Independent factored matched comparator with identical kinds/effect law."""
    def exact(kind,r):
        end=b.cut if kind=='effect-read' else b.last
        if (r.kind!=kind or r.duty!=b.duty or r.effect!=b.effect
            or r.site!=b.site or r.arbiter!=b.arbiter or r.epoch!=b.epoch):return False
        return max(r.sampled-r.arrives,r.arrives-b.cut,b.cut-end,end-r.until)<=0
    for r in rs:
        if exact('interlock',r) and not any(
            w not in r.writers for w in tuple(b.old)+tuple(b.new)):
            return 'interlocked'
    readings=[]
    for r in rs:
        if not exact('effect-read',r) or r.value not in (0,1):
            continue
        for f in rs:
            if (exact('fence',f) and f.sampled<=r.sampled
                    and not any(w not in f.writers for w in b.old)):
                readings.append(r.value)
                break
    if 0 in readings and 1 not in readings:return 'issue'
    if 1 in readings and 0 not in readings:return 'avoid-repeat'
    return 'hold'
