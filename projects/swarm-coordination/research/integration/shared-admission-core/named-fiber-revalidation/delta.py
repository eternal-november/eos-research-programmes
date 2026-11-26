"""Executable certificate for finite complete replacement of named history fibers.

Trusted schema: each history belongs to exactly one stable binding; every
changed binding, including new histories, is covered by a full replacement.
Runtime callers must authorize an edit independently of its payload.
"""
from collections import Counter, defaultdict
from dataclasses import dataclass

@dataclass(frozen=True)
class WholeFiber:
    version: int
    rows: tuple     # may be empty only with a certified unreachable disposition
    retired: bool=False

    def valid(self):
        return self.version >= 0 and bool(self.rows) != bool(self.retired)

@dataclass(frozen=True)
class Edit:
    before: int
    replacement: WholeFiber

class Certificate:
    def __init__(self, support, view, check, names, cut):
        self.view, self.check, self.names, self.cut = view, check, tuple(names), cut
        self.coverage = {}
        self.total = Counter()
        self.fail = defaultdict(Counter)
        self.work = Counter()
        self.issued = {}
        for key, fiber in support.items():
            if not fiber.valid(): raise ValueError("incomplete fiber")
            profile=self.profile(fiber.rows)
            self.update(profile,+1)
            self.coverage[key]=(fiber.version,profile)

    def profile(self, rows):
        cells=defaultdict(Counter)
        for r in rows:
            cell=cells[self.view(r)]
            cell[None]=1
            for n in self.names:
                self.work["checks"]+=1
                if not self.check(r,n):
                    cell[n]=1
        return dict(cells)

    def update(self, profile, sign):
        for view, counts in profile.items():
            self.total[view]+=sign*counts[None]
            for name,val in counts.items():
                if name is not None:
                    self.fail[view][name]+=sign*val
                    if not self.fail[view][name]: del self.fail[view][name]
            if not self.total[view]:
                assert not self.fail[view]
                del self.total[view]
                del self.fail[view]

    def revise(self, edits, *, at, qualified):
        # Batch atomicity: validate every base and compute before changing any
        # verdicts. Reject duplicate names at the producer's mapping boundary.
        if not qualified or at>self.cut or self.issued:
            return False
        for key,edit in edits.items():
            current=self.coverage[key][0] if key in self.coverage else -1
            if (current!=edit.before or edit.replacement.version<=current
                or not edit.replacement.valid()):
                return False
        new={k:(e.replacement.version,self.profile(e.replacement.rows))
             for k,e in edits.items()}
        for k,x in new.items():
            if k in self.coverage:
                self.update(self.coverage[k][1],-1)
            self.update(x[1],+1)
            self.coverage[k]=x
        return True

    def admitted(self, v):
        if not self.total[v]:
            return None       # no live support: cannot issue from this cell
        return tuple(n for n in self.names if not self.fail[v][n])

    def issue(self, v, n, *, at):
        if at!=self.cut or self.issued or n not in (self.admitted(v) or ()):
            return False
        self.issued[v]=n
        return True

def direct(support, view, check, names):
    """Exact same-input factored direct cache's per-fiber replacement kernel."""
    cells={}
    for key,f in support.items():
        m=defaultdict(dict)
        for row in f.rows:
            v=view(row)
            for a in names:
                x=check(row,a)
                m[v][a]=m[v].get(a,True) and x
        cells[key]=dict(m)
    return cells

def project(cached, v, names):
    relevant=[fiber[v] for fiber in cached.values() if v in fiber]
    return tuple(n for n in names if all(x[n] for x in relevant)) if relevant else None
