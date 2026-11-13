"""Exact finite checks supporting the presentation/cell reduction. Python stdlib only."""
from itertools import product
from collections import defaultdict

def partitions(xs):
    xs=tuple(xs)
    if not xs:
        yield frozenset();return
    x,*rest=xs
    for p in partitions(rest):
        yield p|{frozenset([x])}
        for b in p:
            yield (p-{b})|{b|{x}}

def le(p,q):
    return all(any(b<=c for c in q) for b in p)

def presentations(a,b):
    for q in partitions(b):
        blocks=tuple(q)
        for outputs in product((None,)+blocks, repeat=len(a)):
            yield (frozenset(x for x,y in zip(a,outputs) if y is not None),q,
                   {x:y for x,y in zip(a,outputs) if y is not None})

def denote(p):
    x,q,f=p
    return frozenset((a,b) for a in x for b in f[a])

def p_le(p,r):
    x,q,f=p;xx,qq,ff=r
    return x<=xx and le(q,qq) and all(f[a]<=ff[a] for a in x)

def finest(r,b):
    d=frozenset(a for a,_ in r)
    f={a:frozenset(y for x,y in r if x==a) for a in d}
    used=frozenset().union(*f.values()) if f else frozenset()
    q=frozenset(f.values())|frozenset(frozenset([y]) for y in b if y not in used)
    return d,q,f

def embed(p,a,b):
    x,q,f=p
    return frozenset(frozenset([('B',y) for y in block]+[('A',s) for s in x if f[s]==block]) for block in q)|frozenset(frozenset([('A',s)]) for s in a if s not in x)

def normalize(q):
    out=set()
    for block in q:
        if any(tag=='B' for tag,_ in block):out.add(block)
        else:out.update(frozenset([x]) for x in block)
    return frozenset(out)

def relation_corel(q):
    return frozenset((a,b) for block in q for ta,a in block for tb,b in block if ta=='A' and tb=='B')

def compose_corel(p,q):
    # p on A+B, q on A+B; glue p's B to q's A using common labels.
    remap1=lambda x:('L',x[1]) if x[0]=='A' else ('M',x[1])
    remap2=lambda x:('M',x[1]) if x[0]=='A' else ('R',x[1])
    blocks=[set(map(remap1,b)) for b in p]+[set(map(remap2,b)) for b in q]
    changed=True
    while changed:
        changed=False
        for i in range(len(blocks)):
            for j in range(i+1,len(blocks)):
                if blocks[i]&blocks[j]:
                    blocks[i]|=blocks[j];blocks.pop(j);changed=True;break
            if changed:break
    return frozenset(frozenset(('A' if t=='L' else 'B',x) for t,x in block if t!='M') for block in blocks if any(t!='M' for t,x in block))

def old_then(p,r,a,b,c):
    x,q,f=p;u,s,g=r
    qb={v:block for block in q for v in block}
    sc={v:block for block in s for v in block}
    w={qb[v] for v in u}
    d=frozenset(v for v in x if f[v] in w)
    edges=[{('W',qb[v]),('V',g[v])} for v in u]
    comps=[{('W',v)} for v in w]+[{('V',v)} for v in s]+edges
    changed=True
    while changed:
        changed=False
        for i in range(len(comps)):
            for j in range(i+1,len(comps)):
                if comps[i]&comps[j]:
                    comps[i]|=comps[j];comps.pop(j);changed=True;break
            if changed:break
    cb={v:frozenset(z for z in c if ('V',sc[z]) in comp) for comp in comps for v in comp}
    newq=frozenset(cb[('V',sc[z])] for z in c)
    return d,newq,{v:cb[('W',f[v])] for v in d}

def check(condition):
    if not condition:
        raise AssertionError("Finite presentation/cell check failed")

counts=defaultdict(int)
for na in range(4):
 for nb in range(4):
    a=tuple(range(na));b=tuple(range(nb));ps=list(presentations(a,b))
    rs=set(denote(p) for p in ps)
    for p in ps:
      check(denote(finest(denote(p),b))==denote(p))
      for r in rs:
        check(p_le(finest(r,b),p)==(r<=denote(p)));counts['adjunction']+=1
      for pp in ps:
        check(p_le(p,pp)==le(embed(p,a,b),embed(pp,a,b)));counts['fully_faithful_corel']+=1
      for q in partitions(tuple(('A',s) for s in a)+tuple(('B',t) for t in b)):
        check(le(embed(p,a,b),q)==le(embed(p,a,b),normalize(q)));counts['coreflection']+=1
for na in range(3):
 for nb in range(3):
  for nc in range(3):
    a=tuple(range(na));b=tuple(range(nb));c=tuple(range(nc))
    for p in presentations(a,b):
      for q in presentations(b,c):
        check(embed(old_then(p,q,a,b,c),a,c)==normalize(compose_corel(embed(p,a,b),embed(q,b,c))))
        counts['normalization_formula']+=1
print('All exact bounded presentation/cell checks passed.')
for k,v in counts.items():print(k,v)

# Minimal failure of preserving the context-only partial-function control.
a=(0,1);b=(0,);c=(0,)
g=(frozenset(a),frozenset([frozenset(b)]),{0:frozenset(b),1:frozenset(b)})
h=(frozenset(),frozenset([frozenset(c)]),{})
raw=compose_corel(embed(g,a,b),embed(h,b,c))
expected=embed(old_then(g,h,a,b,c),a,c)
check(frozenset([('A',0),('A',1)]) in raw)
check(raw!=expected and normalize(raw)==expected)
# Lost input-only correlation can matter under a subsequent precomposition.
# Use original three-arrow fixture for direct nonmultiplicativity.
a=(0,1);b=(0,1,2,3);c=(0,1,2);d=(0,)
f=(frozenset(a),frozenset([frozenset([0,1]),frozenset([2,3])]),{0:frozenset([0,1]),1:frozenset([2,3])})
g=(frozenset(b),frozenset(frozenset([i]) for i in c),{0:frozenset([0]),1:frozenset([1]),2:frozenset([1]),3:frozenset([2])})
h=(frozenset([2]),frozenset([frozenset(d)]),{2:frozenset(d)})
fi=embed(f,a,b);gi=embed(g,b,c);hi=embed(h,c,d)
left=normalize(compose_corel(normalize(compose_corel(fi,gi)),hi))
right=normalize(compose_corel(fi,normalize(compose_corel(gi,hi))))
check(left!=right)
check(normalize(compose_corel(fi,compose_corel(gi,hi)))==left)
print('Minimal Ctx-control failure and nonmultiplicativity checks passed.')
