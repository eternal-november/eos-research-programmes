"""Independent finite executable model of Nat-decorated relational equipment.

This is finite evidence, not a proof of E1.  Interfaces carry explicit tags;
relations, functions, ordered paths, and every natural-valued cell decoration
are retained.  No equivalence classes or equal-color occurrence deduplication.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product

@dataclass(frozen=True, order=True)
class Obj:
    tag: str
    size: int

@dataclass(frozen=True)
class Vertical:
    source: Obj
    target: Obj
    values: tuple[int, ...]
    def __post_init__(self):
        if not (len(self.values) == self.source.size):
            raise AssertionError('Model invariant failed: len(self.values) == self.source.size')
        if not (all(0 <= v < self.target.size for v in self.values)):
            raise AssertionError('Model invariant failed: all(0 <= v < self.target.size for v in self.values)')
    def __call__(self, x): return self.values[x]

@dataclass(frozen=True)
class Horizontal:
    source: Obj
    target: Obj
    pairs: frozenset[tuple[int, int]]
    def __post_init__(self):
        if not (all(0 <= x < self.source.size and 0 <= y < self.target.size for x,y in self.pairs)):
            raise AssertionError('Model invariant failed: all(0 <= x < self.source.size and 0 <= y < self.target.size for x,y in self.pairs)')

@dataclass(frozen=True)
class Path:
    vertices: tuple[Obj, ...]
    edges: tuple[Horizontal, ...]
    def __post_init__(self):
        if not (len(self.vertices) == len(self.edges)+1):
            raise AssertionError('Model invariant failed: len(self.vertices) == len(self.edges)+1')
        if not (all(e.source == self.vertices[i] and e.target == self.vertices[i+1] for i,e in enumerate(self.edges))):
            raise AssertionError('Model invariant failed: all(e.source == self.vertices[i] and e.target == self.vertices[i+1] for i,e in enumerate(self.edges))')

@dataclass(frozen=True)
class Cell:
    path: Path
    output: Horizontal
    left: Vertical
    right: Vertical
    weight: int
    def __post_init__(self):
        if not (self.weight >= 0):
            raise AssertionError('Model invariant failed: self.weight >= 0')
        if not (self.path.vertices[0] == self.left.source and self.left.target == self.output.source):
            raise AssertionError('Model invariant failed: self.path.vertices[0] == self.left.source and self.left.target == self.output.source')
        if not (self.path.vertices[-1] == self.right.source and self.right.target == self.output.target):
            raise AssertionError('Model invariant failed: self.path.vertices[-1] == self.right.source and self.right.target == self.output.target')
        if not (evaluate(self.path).pairs <= restrict(self.output,self.left,self.right).pairs):
            raise AssertionError('Model invariant failed: evaluate(self.path).pairs <= restrict(self.output,self.left,self.right).pairs')

@lru_cache(None)
def maps(a,b): return tuple(Vertical(a,b,vs) for vs in product(range(b.size),repeat=a.size))
@lru_cache(None)
def relations(a,b):
    coords = tuple(product(range(a.size),range(b.size)))
    return tuple(Horizontal(a,b,frozenset(p for i,p in enumerate(coords) if mask & (1 << i))) for mask in range(1 << len(coords)))
def identity(a): return Vertical(a,a,tuple(range(a.size)))
def diagonal(a): return Horizontal(a,a,frozenset((x,x) for x in range(a.size)))
def composite(f,h):
    """f after h, the ordinary typed vertical composition."""
    if not (h.target == f.source):
        raise AssertionError('Model invariant failed: h.target == f.source')
    return Vertical(h.source,f.target,tuple(f(h(x)) for x in range(h.source.size)))
@lru_cache(None)
def restrict(H,f,g):
    if not (f.target == H.source and g.target == H.target):
        raise AssertionError('Model invariant failed: f.target == H.source and g.target == H.target')
    return Horizontal(f.source,g.source,frozenset((x,y) for x in range(f.source.size) for y in range(g.source.size) if (f(x),g(y)) in H.pairs))
@lru_cache(None)
def relcomp(R,S):
    if not (R.target == S.source):
        raise AssertionError('Model invariant failed: R.target == S.source')
    return Horizontal(R.source,S.target,frozenset((x,z) for x,y in R.pairs for y2,z in S.pairs if y==y2))
@lru_cache(None)
def evaluate(p):
    R=diagonal(p.vertices[0])
    for H in p.edges: R=relcomp(R,H)
    return R

def evaluate_tuple_oracle(p):
    """Independent full-tuple oracle, including the boundary coordinate at arity 0."""
    return frozenset((xs[0],xs[-1]) for xs in product(*(range(a.size) for a in p.vertices)) if all((xs[i],xs[i+1]) in H.pairs for i,H in enumerate(p.edges)))

def paths(vertices):
    return (Path(tuple(vertices),tuple(es)) for es in product(*(relations(a,b) for a,b in zip(vertices,vertices[1:]))))

def insert_unit(p,j):
    a=p.vertices[j]
    return Path(p.vertices[:j+1]+(a,)+p.vertices[j+1:],p.edges[:j]+(diagonal(a),)+p.edges[j:])

def reindex_path(p,fs):
    if not (len(fs)==len(p.vertices) and all(f.target==a for f,a in zip(fs,p.vertices))):
        raise AssertionError('Model invariant failed: len(fs)==len(p.vertices) and all(f.target==a for f,a in zip(fs,p.vertices))')
    return Path(tuple(f.source for f in fs),tuple(restrict(H,f,g) for H,f,g in zip(p.edges,fs,fs[1:])))

def marked(cell):
    if not (cell.left==identity(cell.path.vertices[0]) and cell.right==identity(cell.path.vertices[-1])):
        raise AssertionError('Model invariant failed: cell.left==identity(cell.path.vertices[0]) and cell.right==identity(cell.path.vertices[-1])')
    return cell.weight==0 and evaluate(cell.path)==cell.output

def factor(cell,f,g,h,k):
    if not (cell.left==composite(f,h) and cell.right==composite(g,k)):
        raise AssertionError('Model invariant failed: cell.left==composite(f,h) and cell.right==composite(g,k)')
    return Cell(cell.path,restrict(cell.output,f,g),h,k,cell.weight)

def unfactor(cell,H,f,g):
    if not (cell.output==restrict(H,f,g)):
        raise AssertionError('Model invariant failed: cell.output==restrict(H,f,g)')
    return Cell(cell.path,H,composite(f,cell.left),composite(g,cell.right),cell.weight)

def compose_weight(outer,children): return outer+sum(children)

def substitute(alpha, children):
    """Original occurrence-wise globular substitution; repeats never deduplicated."""
    if not (alpha.left==identity(alpha.path.vertices[0]) and alpha.right==identity(alpha.path.vertices[-1])):
        raise AssertionError('Model invariant failed: alpha.left==identity(alpha.path.vertices[0]) and alpha.right==identity(alpha.path.vertices[-1])')
    if not (len(children)==len(alpha.path.edges)):
        raise AssertionError('Model invariant failed: len(children)==len(alpha.path.edges)')
    vertices=[alpha.path.vertices[0]]; edges=[]
    for i,beta in enumerate(children):
        if not (beta.output==alpha.path.edges[i]):
            raise AssertionError('Model invariant failed: beta.output==alpha.path.edges[i]')
        if not (beta.left==identity(beta.path.vertices[0]) and beta.right==identity(beta.path.vertices[-1])):
            raise AssertionError('Model invariant failed: beta.left==identity(beta.path.vertices[0]) and beta.right==identity(beta.path.vertices[-1])')
        if not (beta.path.vertices[0]==vertices[-1]):
            raise AssertionError('Model invariant failed: beta.path.vertices[0]==vertices[-1]')
        vertices.extend(beta.path.vertices[1:]); edges.extend(beta.path.edges)
    p=Path(tuple(vertices),tuple(edges))
    return Cell(p,alpha.output,alpha.left,alpha.right,compose_weight(alpha.weight,tuple(b.weight for b in children)))
