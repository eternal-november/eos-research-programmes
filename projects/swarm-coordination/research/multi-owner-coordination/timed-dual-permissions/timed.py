"""Consent-admission intervals and finite observer scheduling."""
from dataclasses import dataclass
from itertools import combinations

@dataclass(frozen=True)
class Timing:
    decision: int
    clear: int
    old: tuple  # actuator-recognized half-open interval, fixed role/scope
    new: tuple
    handshake: int
    remaining: int
    due: int

def interval(w):
    a,e=w.old; b,f=w.new
    lo=max(w.decision,w.clear,a,b)
    hi=min(e-w.handshake,f-w.handshake-w.remaining,
           w.due-w.handshake-w.remaining)
    return (lo,hi)

def execute(w,start):
    # The independent load crosses disjoint cells during the handoff.
    independent=list(zip((0,3,6,8,10),('separate-origin','separate-approach',
        'separate-support','separate-exit','separate-load-destination')))
    pos='pickup'
    if start < w.decision or start < w.clear:
        return independent,pos
    for tick in range(start,start+w.handshake+w.remaining):
        if not w.new[0]<=tick<w.new[1] or tick>=w.due:
            return independent,pos
        if tick<start+w.handshake and not w.old[0]<=tick<w.old[1]:
            return independent,pos
        if tick+1==start+w.handshake:
            pos='transferred'
        if tick+1==start+w.handshake+w.remaining and pos=='transferred':
            pos='delivered'
    return independent,pos

def meet(items):
    return max(l for l,_ in items),min(r for _,r in items)

def stabbing(items):
    points=[]
    for left,right in sorted(items,key=lambda a:a[1]):
        if left>right:
            raise ValueError('empty feasible interval')
        if not points or points[-1]<left:
            points.append(right)
    return tuple(points)

def observers(rows):
    by={}
    for z,v,i in rows:
        by.setdefault((z,v),[]).append(i)
    pinned={key:meet(xs) for key,xs in by.items()}
    if any(a>b for a,b in pinned.values()):
        return None
    zs=sorted({z for z,_ in pinned})
    g={z:set() for z in zs}
    for z,y in combinations(zs,2):
        for u,v in pinned:
            if u==z and (y,v) in pinned:
                a,b=meet([pinned[u,v],pinned[y,v]])
                if a>b:
                    g[z].add(y);g[y].add(z)
    return pinned,g

def color(g):
    # Search named vertices ordered by degree. Only the next unused color
    # needs trying because unused labels can be permuted.
    zs=sorted(g,key=lambda z:(-len(g[z]),z))
    out={}
    def search(depth,k):
        if depth==len(zs):
            return True
        z=zs[depth]
        bad={out[u] for u in g[z] if u in out}
        used=max(out.values(),default=-1)+1
        for c in range(min(used+1,k)):
            if c not in bad:
                out[z]=c
                if search(depth+1,k):
                    return True
                out.pop(z)
        return False
    for k in range(1,len(zs)+1):
        if search(0,k):
            return dict(out)
    return {}

def schedule(rows):
    p=observers(rows)
    if p is None:
        return None
    j,g=p
    sender=color(g)
    cells={}
    for (z,v),i in j.items():
        cells.setdefault((sender[z],v),[]).append(i)
    times={c:meet(xs)[0] for c,xs in cells.items()}
    assert all(meet(xs)[0]<=meet(xs)[1] for xs in cells.values())
    return sender,times
