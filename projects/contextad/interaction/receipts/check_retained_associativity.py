"""Exact List-receipt associativity/pentagon regression, not a proof of the theorem."""
from fractions import Fraction as F
from itertools import product
from dataclasses import dataclass
import json

@dataclass
class Arrow:
    A: tuple
    B: tuple
    P: dict
    Q: dict
    body: dict
    def label(self, out):
        return (out[1],) if out[0]=='b' else self.Q[out[1]]
    def validate(self):
        for a in self.A:
            assert sum(self.P[a].values())==1
            for x in self.P[a]:
                o=self.body[a,x]
                assert o[1] in (self.B if o[0]=='b' else self.Q)
        assert all(all(b in self.B for b in w) for w in self.Q.values())
        return self

def choices(P, word):
    return product(*(P[b] for b in word))
def weight(P, word, xs):
    z=F(1)
    for b,x in zip(word,xs): z*=P[b][x]
    return z

def comp(f,g):
    assert f.B==g.A
    P={a:{} for a in f.A}; body={}; Q={('later',q):w for q,w in g.Q.items()}
    for q,word in f.Q.items():
        for rs in choices(g.P,word):
            Q['earlier',q,rs]=sum((g.label(g.body[b,r]) for b,r in zip(word,rs)),())
    for a in f.A:
        for x,px in f.P[a].items():
            o=f.body[a,x]; word=f.label(o)
            for rs in choices(g.P,word):
                xx=(x,rs); P[a][xx]=px*weight(g.P,word,rs)
                if o[0]=='b':
                    oo=g.body[o[1],rs[0]]
                    body[a,xx]=oo if oo[0]=='b' else ('q',('later',oo[1]))
                else: body[a,xx]=('q',('earlier',o[1],rs))
    return Arrow(f.A,g.B,P,Q,body).validate()

@dataclass
class Cell:
    src: Arrow
    dst: Arrow
    pm: object
    qm: object
    def check(self, bijective=False):
        assert self.src.A==self.dst.A and self.src.B==self.dst.B
        vals=[self.qm(q) for q in self.src.Q]
        assert all(v in self.dst.Q for v in vals)
        assert all(self.src.Q[q]==self.dst.Q[self.qm(q)] for q in self.src.Q)
        if bijective: assert len(vals)==len(set(vals))==len(self.dst.Q)
        for a in self.src.A:
            push={x:F(0) for x in self.dst.P[a]}
            ys=[]
            for x,p in self.src.P[a].items():
                y=self.pm(a,x); assert y in push; push[y]+=p; ys.append(y)
                o=self.src.body[a,x]
                oo=o if o[0]=='b' else ('q',self.qm(o[1]))
                assert oo==self.dst.body[a,y]
            assert push==self.dst.P[a]
            if bijective: assert len(ys)==len(set(ys))==len(self.dst.P[a])
        return self

def ident(f): return Cell(f,f,lambda a,x:x,lambda q:q)
def then(c,d):
    assert c.dst==d.src
    return Cell(c.src,d.dst,lambda a,x:d.pm(a,c.pm(a,x)),lambda q:d.qm(c.qm(q)))
def horiz(c,d):
    f,g=c.src,d.src
    def pm(a,xx):
        x,rs=xx; word=f.label(f.body[a,x])
        return c.pm(a,x),tuple(d.pm(b,r) for b,r in zip(word,rs))
    def qm(q):
        if q[0]=='later': return 'later',d.qm(q[1])
        _,old,rs=q
        return 'earlier',c.qm(old),tuple(d.pm(b,r) for b,r in zip(f.Q[old],rs))
    return Cell(comp(c.src,d.src),comp(c.dst,d.dst),pm,qm).check()

def grouped(g, word, rs, zs):
    out=[]; j=0
    for b,r in zip(word,rs):
        n=len(g.label(g.body[b,r])); out.append((r,zs[j:j+n])); j+=n
    assert j==len(zs)
    return tuple(out)
def assoc(f,g,h):
    src=comp(comp(f,g),h); dst=comp(f,comp(g,h))
    def pm(a,xx):
        (x,rs),zs=xx
        return x,grouped(g,f.label(f.body[a,x]),rs,zs)
    def qm(q):
        if q[0]=='later': return 'later',('later',q[1])
        _,fgq,zs=q
        if fgq[0]=='later': return 'later',('earlier',fgq[1],zs)
        _,old,rs=fgq
        return 'earlier',old,grouped(g,f.Q[old],rs,zs)
    return Cell(src,dst,pm,qm).check(True)

def mk(A,B,P,Q,fun):
    return Arrow(tuple(A),tuple(B),P,Q,{(a,x):fun(a,x) for a in A for x in P[a]}).validate()
f=mk(('a',),('b0','b1'),{'a':{0:F(1,2),1:F(1,2),2:F(0)}},
     {'active':('b0','b1'),'dormant':('b1','b1'),'nullary':(),'same':('b0','b1')},
     lambda a,x:('b','b0') if x==0 else ('q','active' if x==1 else 'nullary'))
g=mk(f.B,('c0','c1'),{'b0':{0:F(1,2),1:F(1,2),2:F(0)},'b1':{0:F(1,3),1:F(2,3)}},
     {'active':('c0','c1'),'dormant':('c1',),'nullary':()},
     lambda b,r:('q','nullary') if r==2 else (('b','c0' if b=='b0' else 'c1') if r==0 else ('q','active')))
h=mk(g.B,('d0','d1'),{'c0':{0:F(1,2),1:F(1,2)},'c1':{0:F(1),1:F(0)}},
     {'active':('d0',),'dormant':('d1','d0'),'nullary':()},
     lambda c,r:('b','d0' if c=='c0' else 'd1') if r==0 else ('q','active' if c=='c0' else 'nullary'))
k=mk(h.B,('e',),{'d0':{0:F(1,2),1:F(1,2)},'d1':{0:F(1,2),1:F(1,2)}},
     {'dormant':('e','e'),'nullary':()},lambda d,r:('b','e'))
a=assoc(f,g,h)
left=then(assoc(comp(f,g),h,k),assoc(f,g,comp(h,k))).check(True)
right=then(then(horiz(assoc(f,g,h),ident(k)),assoc(f,comp(g,h),k)),horiz(ident(f),assoc(g,h,k))).check(True)
assert left.src==right.src and left.dst==right.dst
assert all(left.pm(a,x)==right.pm(a,x) for a in left.src.A for x in left.src.P[a])
assert all(left.qm(q)==right.qm(q) for q in left.src.Q)
# Explicitly ensure unreachable grades and zero-mass carriers were not discarded.
assert any(p==0 for p in left.src.P['a'].values())
used={o[1] for o in left.src.body.values() if o[0]=='q'}
assert len(used)<len(left.src.Q)
result={'status':'passed','triple_context_points':len(a.src.P['a']), 'triple_receipt_tags':len(a.src.Q),
        'pentagon_context_points':len(left.src.P['a']),'pentagon_receipt_tags':len(left.src.Q),
        'pentagon_zero_weight_context_points':sum(p==0 for p in left.src.P['a'].values()),
        'pentagon_unreachable_receipts':len(left.src.Q)-len(used),
        'checked':['weight pushforward','body square','all tag labels','bijective context and receipt maps','pentagon on both sorts'],
        'scope':'one exact List instance, including dormant/nullary/repeated tags and raw zero weights; not general coherence proof'}
print(json.dumps(result,indent=2))
