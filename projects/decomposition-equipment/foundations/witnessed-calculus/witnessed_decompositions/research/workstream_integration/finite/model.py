"""Literal typed finite model. C evidence only; no category congruence definition."""
from dataclasses import dataclass, replace
from itertools import combinations, combinations_with_replacement, product
from functools import lru_cache

@dataclass(frozen=True)
class Monoid:
    name: str
    table: tuple
    @property
    def size(self): return len(self.table)
    def mul(self,a,b): return self.table[a][b]
    def prod(self,values):
        r=0
        for x in values:r=self.mul(r,x)
        return r
Z3=Monoid('Z3',((0,1,2),(1,2,0),(2,0,1)))
E2=Monoid('E2',((0,1),(1,1)))
ONE=Monoid('One',((0,),))
MONOIDS=(Z3,E2,ONE)

@dataclass(frozen=True)
class Graph:
    n:int
    edges:tuple=()
    def restrict(self,vertices):
        v=tuple(sorted(vertices)); E=set(self.edges)
        return Graph(len(v),tuple((i,j) for i in range(len(v)) for j in range(i+1,len(v)) if (v[i],v[j]) in E))
@dataclass(frozen=True)
class Arrow:
    a:int
    b:int
    z:int=0
    def then(self,g):
        assert self.b==g.a
        return Arrow(self.a,g.b,(self.z+g.z)%2)

def compose(arrows,base):
    out=Arrow(base,base)
    for a in arrows:out=out.then(a)
    return out

@dataclass(frozen=True)
class Flat:
    graph:Graph
    whole:Arrow
    blocks:tuple
    arrows:tuple
    value:int=0
    @property
    def profile(self):return tuple((self.graph.restrict(b),a) for b,a in zip(self.blocks,self.arrows))
    def valid(self):
        if len(self.blocks)!=len(self.arrows):return False
        vs=tuple(v for b in self.blocks for v in b)
        if sorted(vs)!=list(range(self.graph.n)):return False
        if any(tuple(sorted(b))!=b for b in self.blocks):return False
        if not self.blocks:return self.graph.n==0 and self.whole==Arrow(self.whole.a,self.whole.a)
        try:return self.whole==compose(self.arrows,self.whole.a)
        except AssertionError:return False

def flat_identity(g,a):return Flat(g,a,(tuple(range(g.n)),),(a,),0)

def flat_compose(w,entries,M):
    assert w.valid() and len(entries)==len(w.blocks)
    bs=[];ars=[];vals=[w.value]
    for U,f,e in zip(w.blocks,w.arrows,entries):
        assert e.valid() and (e.graph,e.whole)==(w.graph.restrict(U),f)
        bs.extend(tuple(U[j] for j in V) for V in e.blocks)
        ars.extend(e.arrows)
        vals.append(e.value)
    q=Flat(w.graph,w.whole,tuple(bs),tuple(ars),M.prod(vals));assert q.valid();return q

@dataclass(frozen=True)
class Term:
    kind:str
    graph:Graph
    arrow:Arrow
    children:tuple=()
    left:tuple=()
    value:int=0

def L(g,a):return Term('L',g,a)
def U(a):return Term('U',Graph(0),Arrow(a,a))
def D(v,t):return Term('D',t.graph,t.arrow,(t,),value=v)
def C(g,left,x,y):
    left=tuple(sorted(left));right=tuple(i for i in range(g.n) if i not in left)
    assert len(left)==len(set(left)) and all(0<=i<g.n for i in left)
    assert x.graph==g.restrict(left) and y.graph==g.restrict(right)
    return Term('C',g,x.arrow.then(y.arrow),(x,y),left)

def leaves(t):
    if t.kind=='L':return (t,)
    return sum((leaves(c) for c in t.children),())

def node_count(t):return (0 if t.kind=='L' else 1)+sum(node_count(c) for c in t.children)

def graft(t,forest):
    ls=leaves(t);assert len(ls)==len(forest)
    for l,f in zip(ls,forest):assert (l.graph,l.arrow)==(f.graph,f.arrow)
    it=iter(forest)
    def go(s):
        if s.kind=='L':return next(it)
        return replace(s,children=tuple(go(c) for c in s.children))
    return go(t)

def dispatch_graft(t,forest):
    # MUTATION_POINT repeated occurrences: this positional dispatch must remain positional.
    return graft(t,forest)

def compose_forest(F,H):
    out=[];p=0
    for f in F:
        n=len(leaves(f));out.append(graft(f,H[p:p+n]));p+=n
    assert p==len(H);return tuple(out)

@lru_cache(None)
def evaluation(t,M):
    if t.kind=='L':return flat_identity(t.graph,t.arrow)
    if t.kind=='U':return Flat(t.graph,t.arrow,(),(),0)
    if t.kind=='D':
        w=evaluation(t.children[0],M)
        return replace(w,value=M.mul(t.value,w.value))
    x,y=t.children;right=tuple(v for v in range(t.graph.n) if v not in t.left)
    outer=Flat(t.graph,t.arrow,(t.left,right),(x.arrow,y.arrow),0)
    return flat_compose(outer,(evaluation(x,M),evaluation(y,M)),M)

def address_evaluation(t,M):
    blocks=[];arrows=[];values=[]
    def walk(q,embedding):
        if q.kind=='L':blocks.append(tuple(embedding));arrows.append(q.arrow)
        elif q.kind=='D':values.append(q.value);walk(q.children[0],embedding)
        elif q.kind=='C':
            walk(q.children[0],tuple(embedding[i] for i in q.left))
            walk(q.children[1],tuple(embedding[i] for i in range(q.graph.n) if i not in q.left))
    walk(t,tuple(range(t.graph.n)))
    ans=Flat(t.graph,t.arrow,tuple(blocks),tuple(arrows),M.prod(values));assert ans.valid();return ans

def canonical(w,M):
    assert w.valid()
    if not w.blocks:q=U(w.whole.a)
    elif len(w.blocks)==1:q=L(w.graph,w.whole)
    else:
        tail=tuple(sorted(v for b in w.blocks[1:] for v in b));ix={v:i for i,v in enumerate(tail)}
        sub=Flat(w.graph.restrict(tail),compose(w.arrows[1:],w.arrows[0].b),tuple(tuple(ix[v] for v in b) for b in w.blocks[1:]),w.arrows[1:],0)
        q=C(w.graph,w.blocks[0],L(w.graph.restrict(w.blocks[0]),w.arrows[0]),canonical(sub,M))
    return q if w.value==0 else D(w.value,q)

def root_steps(t,M):
    out=[]
    if t.kind=='D':
        x=t.children[0]
        if t.value==0:out.append(('D0',x))
        if x.kind=='D':out.append(('DA',D(M.mul(t.value,x.value),x.children[0])))
    if t.kind=='C':
        x,y=t.children
        if x.kind=='U':out.append(('UL',y))
        if y.kind=='U':out.append(('UR',x))
        if x.kind=='D':out.append(('DL',D(x.value,C(t.graph,t.left,x.children[0],y))))
        if y.kind=='D':out.append(('DR',D(y.value,C(t.graph,t.left,x,y.children[0]))))
        if x.kind=='C':
            a,b=x.children;u=tuple(t.left[i] for i in x.left)
            v=tuple(t.left[i] for i in range(x.graph.n) if i not in x.left)
            rest=tuple(i for i in range(t.graph.n) if i not in u)
            out.append(('R',C(t.graph,u,a,C(t.graph.restrict(rest),tuple(rest.index(i) for i in v),b,y))))
    return out

def steps(t,M):
    out=[((),rule,q) for rule,q in root_steps(t,M)]
    for i,c in enumerate(t.children):
        for addr,rule,q in steps(c,M):
            ch=list(t.children);ch[i]=q
            out.append(((i,)+addr,rule,replace(t,children=tuple(ch))))
    return out

def at(t,addr):
    for i in addr:t=t.children[i]
    return t

def replace_at(t,addr,q):
    if not addr:return q
    ch=list(t.children);ch[addr[0]]=replace_at(ch[addr[0]],addr[1:],q)
    return replace(t,children=tuple(ch))

def apply_step(t,addr,rule,M):
    options=[q for r,q in root_steps(at(t,addr),M) if r==rule]
    assert len(options)==1,(rule,addr)
    return replace_at(t,addr,options[0])

def measure(t):
    if t.kind in ('L','U'):return (0,0,0,0)
    if t.kind=='D':
        b,a,h,d=measure(t.children[0]);return (b,a,h,d+1)
    b1,a1,h1,d1=measure(t.children[0]);b2,a2,h2,d2=measure(t.children[1])
    return (1+b1+b2,a1+a2+b1,h1+h2+d1+d2,d1+d2)

def normalize(t,M):
    trace=[]
    while True:
        opts=steps(t,M)
        if not opts:return t,tuple(trace)
        addr,rule,q=opts[0];assert measure(q)<measure(t)
        trace.append((addr,rule));t=q

def arrow_key(entries):
    # MUTATION_POINT arrow profiles: entries, not merely their composite, are arrow data.
    return tuple(entries)

MIXED_SCHEMAS={'MOut','MIn'}
@dataclass(frozen=True)
class Raw:
    forest:tuple
@dataclass(frozen=True)
class Eq:
    target:Term
    addr:tuple
    rule:str
    inverse:bool=False

def path_normalize(source,path,M):
    current=source;F=tuple(leaves(source))
    for e in path:
        if isinstance(e,Raw):
            current=dispatch_graft(current,e.forest);F=compose_forest(F,e.forest)
        else:
            assert isinstance(e,Eq)
            if e.inverse:assert apply_step(e.target,e.addr,e.rule,M)==current
            else:assert apply_step(current,e.addr,e.rule,M)==e.target
            assert tuple((x.graph,x.arrow) for x in leaves(current))==tuple((x.graph,x.arrow) for x in leaves(e.target))
            current=e.target
    if 'MIn' in MIXED_SCHEMAS:
        F=tuple(normalize(f,M)[0] for f in F)
    return F,current

def semantic_path(source,path,M):
    current=source;entries=tuple(flat_identity(l.graph,l.arrow) for l in leaves(source))
    for e in path:
        if isinstance(e,Raw):
            H=tuple(address_evaluation(f,M) for f in e.forest);p=0;out=[]
            for b in entries:
                n=len(b.blocks);out.append(flat_compose(b,H[p:p+n],M));p+=n
            assert p==len(H);entries=tuple(out);current=graft(current,e.forest)
        else:current=e.target
    assert flat_compose(address_evaluation(source,M),entries,M)==address_evaluation(current,M)
    return entries,current

def weakcomps(total,k):
    if k==0:
        if total==0:yield ()
    elif k==1:yield (total,)
    else:
        for i in range(total+1):
            for tail in weakcomps(total-i,k-1):yield (i,)+tail

def graphs(d):
    for n in range(d+1):
        ps=tuple(combinations(range(n),2))
        for bits in product((0,1),repeat=len(ps)):
            yield Graph(n,tuple(e for e,b in zip(ps,bits) if b))

def partitions(n,k):
    for f in product(range(k),repeat=n):yield tuple(tuple(v for v,b in enumerate(f) if b==i) for i in range(k))

def strings(k,grades=False,objects=(0,1,2)):
    for obj in combinations_with_replacement(objects,k+1):
        for zs in product(range(2 if grades else 1),repeat=k):
            yield obj,tuple(Arrow(obj[i],obj[i+1],zs[i]) for i in range(k))

@lru_cache(None)
def catalog(g,a,k,M):
    out=[]
    if k==0:
        if g.n==0 and a==Arrow(a.a,a.a):
            out.extend(Flat(g,a,(),(),v) for v in range(M.size))
        return tuple(out)
    for bs in partitions(g.n,k):
        for obj,ars in strings(k,grades=False):
            if compose(ars,obj[0])==a:
                out.extend(Flat(g,a,bs,ars,v) for v in range(M.size))
    return tuple(out)

def hom_decode(src,tgt,M):
    if (src.graph,src.whole)!=(tgt.graph,tgt.whole):return set()
    ans=set();k=len(src.blocks);l=len(tgt.blocks)
    for lengths in weakcomps(l,k):
        p=0;bare=[];ok=True
        for U,a,n in zip(src.blocks,src.arrows,lengths):
            run=tgt.blocks[p:p+n];ars=tgt.arrows[p:p+n];p+=n
            if sorted(v for B in run for v in B)!=list(U):ok=False;break
            try:total=compose(ars,a.a)
            except AssertionError:ok=False;break
            if total!=a:ok=False;break
            pos={v:i for i,v in enumerate(U)}
            bare.append(Flat(src.graph.restrict(U),a,tuple(tuple(pos[v] for v in B) for B in run),ars,0))
        if not ok:continue
        for vals in product(range(M.size),repeat=k):
            if M.mul(src.value,M.prod(vals))!=tgt.value:continue
            entries=tuple(replace(e,value=v) for e,v in zip(bare,vals))
            assert flat_compose(src,entries,M)==tgt
            ans.add(arrow_key(entries))
    return ans

def tuple_encoder(src,max_l,M):
    k=len(src.blocks)
    for l in range(max_l+1):
        for lengths in weakcomps(l,k):
            pools=[catalog(src.graph.restrict(U),a,n,M) for U,a,n in zip(src.blocks,src.arrows,lengths)]
            for es in product(*pools):yield tuple(es),flat_compose(src,es,M)

def tuple_compose(F,H,M):
    p=0;out=[]
    for e in F:
        n=len(e.blocks);out.append(flat_compose(e,H[p:p+n],M));p+=n
    assert p==len(H);return tuple(out)
