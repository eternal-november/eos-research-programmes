"""Exact robust classification for a fixed integer-time resource-use shape."""
from dataclasses import dataclass

def runs(bits):
    out=[]
    a=None
    for i,b in enumerate((*bits,0)):
        if b and a is None:a=i
        elif not b and a is not None:
            out.append((a,i))
            a=None
    return tuple(out)

@dataclass(frozen=True)
class Binding:
    key: tuple
    resource: int | None  # None: positively witnessed disjointness
    shift: int
    tape: tuple

@dataclass(frozen=True)
class Profile:
    known_start: tuple | None
    blocked: tuple
    support: tuple

    def verdict(self,start):
        # A real conflict is conclusive even when another world was not read.
        if any(a<=start<=b for a,b in self.blocked):return 'conflict'
        if self.known_start is None:return 'safe'
        lo,hi=self.known_start
        return 'safe' if lo<=start<=hi else 'unknown'

def compile_profile(worlds,l,r):
    assert l<r
    worlds=tuple(worlds)
    assert worlds and len({w.key for w in worlds})==len(worlds)
    lows=[]; highs=[]; edges=[]
    witness=[]
    for w in worlds:
        if w.resource is None:continue
        lo=w.shift-l
        hi=w.shift+len(w.tape)-r
        lows.append(lo); highs.append(hi)
        for a,b in runs(w.tape):
            interval=(a+w.shift-r+1,b+w.shift-l-1)
            if interval[0]<=interval[1]:
                edges.append(interval)
                witness.append((w.key,interval))
    # None denotes positively witnessed disjointness in all worlds.
    common=(max(lows),min(highs)) if lows else None
    out=[]
    for a,b in sorted(edges):
        if out and a<=out[-1][1]+1:
            out[-1]=(out[-1][0],max(b,out[-1][1]))
        else:out.append((a,b))
    return Profile(common,tuple(out),tuple(witness))
