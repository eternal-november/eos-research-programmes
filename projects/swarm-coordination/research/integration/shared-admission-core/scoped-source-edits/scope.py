"""Impact compiler for finite, versioned, complete three-relation supports."""
from collections import defaultdict
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class Patch:
    before: int
    after: int
    radio: dict         # key -> replacement set, or None (certified deleted)
    duty: dict          # key -> replacement set, or None
    links: dict         # name -> inclusive alternatives (radio key,duty key), or None

def edit(m,d):
    for k,x in d.items():
        if x is None:
            m.pop(k,None)
        else:
            m[k]=x

class Scope:
    def __init__(self, radio, duty, links, epoch=0):
        self.radio,self.duty,self.links=map(dict,(radio,duty,links))
        self.ixr,self.ixd=defaultdict(set),defaultdict(set)
        self.epoch=epoch
        if any(not x for m in (radio,duty,links) for x in m.values()):
            raise ValueError("Declare a deletion explicitly; an empty fragment is unknown")
        for n,ls in links.items():
            self._pairs(ls)
            self._link(n,ls,True)

    def _link(self,n,ls,add):
        for ix,dim in ((self.ixr,0),(self.ixd,1)):
            for k in {p[dim] for p in ls}:
                if add:
                    ix[k].add(n)
                else:
                    ix[k].remove(n)
                    if not ix[k]:
                        del ix[k]

    def _pairs(self,ls,r=None,d=None):
        r,d=r or {},d or {}
        out=set()
        for kr,kd in ls:
            rr=r.get(kr,self.radio.get(kr))
            dd=d.get(kd,self.duty.get(kd))
            if not rr or not dd:
                raise ValueError("Live link lacks complete source fragment")
            out.update(product(rr,dd))
        return frozenset(out)

    def compile(self, p):
        """Pure prepare. Does not certify upstream declaration or edit delivery."""
        if not (p.before==self.epoch and p.after>p.before):
            raise ValueError("Incompatible snapshot version")
        if any(x is not None and not x for m in (p.radio,p.duty,p.links) for x in m.values()):
            raise ValueError("Empty replacement fragment is unknown")
        # Any incidence not in these old indices must occur in an edited link.
        candidates=set(p.links)
        for k in p.radio:
            candidates.update(self.ixr.get(k,()))
        for k in p.duty:
            candidates.update(self.ixd.get(k,()))
        changed={}
        for n in candidates:
            old=self._pairs(self.links.get(n,()))
            new=self._pairs(p.links.get(n,self.links.get(n)) or (),p.radio,p.duty)
            if old!=new:
                changed[n]=new
        return frozenset(candidates),changed

    def install(self,p):
        # Recheck on direct use. A caller driving another checker must serialize
        # prepare, verification, and install; do not externally publish mid-batch.
        self.compile(p)
        for n in p.links.keys() & self.links.keys():
            self._link(n,self.links[n],False)
        edit(self.radio,p.radio)
        edit(self.duty,p.duty)
        edit(self.links,p.links)
        for n in p.links.keys() & self.links.keys():
            self._link(n,self.links[n],True)
        self.epoch=p.after
