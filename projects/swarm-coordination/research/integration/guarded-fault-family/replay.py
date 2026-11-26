"""Replay using synthetic civil delivery traces; no dependencies."""
from functools import reduce
from operator import or_
from random import Random
from guarded import BDD, Family

def formula(B, z):
    if type(z) is bool:
        return int(z)
    if type(z) is int:
        return B.atom(z)
    k,*args=z
    if k == 'not':
        return B.neg(formula(B, args[0]))
    return reduce(lambda a,v:B.op(k,a,formula(B,v)),args,int(k=='and'))

def scalar(z,a):
    if type(z) is bool:
        return z
    if type(z) is int:
        return bool(a >> z & 1)
    k,*args=z
    if k=='not':
        return not scalar(args[0],a)
    return (all if k=='and' else any)(scalar(v,a) for v in args)

def matches(B,i,a,k):
    return B.val(i,{j:bool(a>>j&1) for j in range(k)})

def tape(B,i,n):
    return sum(1<<a for a in range(1<<n) if matches(B,i,a,n))

def build(n, roots, bad, edges, B=None):
    B=BDD() if B is None else B
    return B,Family(B,roots,n,{i:(u,v,formula(B,g)) for i,(u,v,g) in edges.items()},bad)

def replay_path(edges,path,roots,bad,a):
    if not path:
        return bool(set(roots)&set(bad))
    at=edges[path[0]][0]
    if at not in roots:
        return False
    for i in path:
        u,v,g=edges[i]
        if at!=u or not scalar(g,a):
            return False
        at=v
    return at in bad

def one_world(edges,n,roots,a):
    # Independent forward traversal, with guards evaluated concretely.
    reachable=set(roots)
    for u in range(n):
        if u in reachable:
            reachable.update(v for x,v,g in edges.values() if x==u and scalar(g,a))
    return reachable

def bitset(n,roots,bad,edges,k):
    # Family reference: whole-world sets encoded by integer masks, rebuilt globally.
    N=1<<k
    all_bits=(1<<N)-1
    by_origin=[[] for _ in range(n)]
    for u,v,g in edges.values():
        by_origin[u].append((v,sum(1<<a for a in range(N) if scalar(g,a))))
    r=[all_bits if i in roots else 0 for i in range(n)]
    for u,out in enumerate(by_origin):
        for v,g in out:
            r[v]|=r[u]&g
    return r,reduce(or_,(r[v] for v in bad),0)

def audit(B,F,edges,n,k,roots,bad,adm):
    r,viol=bitset(n,roots,bad,edges,k)
    g=formula(B,adm)
    assert [tape(B,i,k) for i in F.reach]==r
    assert tape(B,F.violation(),k)==viol
    assert tape(B,B.op('and',g,F.violation()),k)==sum(
        (1<<a) for a in range(1<<k)
        if scalar(adm,a) and (one_world(edges,n,roots,a)&set(bad)))
    for a in range(1<<k):
        if viol >> a & 1:
            d={j:bool(a>>j&1) for j in range(k)}
            assert replay_path(edges,F.witness(d),roots,bad,a)
    return 1<<k

def controls():
    # A recombined fault history that never exists in any fixed installation.
    e={'prior':(0,1,0),'release':(1,2,('not',0))}
    B,F=build(3,[0],[2],e)
    audit(B,F,e,3,1,[0],[2],True)
    assert F.violation()==0 and one_world({i:(u,v,True) for i,(u,v,_) in e.items()},3,[0],0)=={0,1,2}
    # Disagreement then qualified narrowing; empty admission is a conflict, not a go.
    e={'bad':(0,1,0)}
    B,F=build(2,[0],[1],e)
    b=F.violation()
    A=[True,0,('not',0),False]
    classified=[]
    for a in A:
        i=formula(B,a)
        audit(B,F,e,2,1,[0],[1],a)
        classified.append('inconsistent' if not i else 'safe' if not B.op('and',i,b)
                          else 'all-bad' if not B.op('and',i,B.neg(b)) else 'mixed')
        assert F.violation()==b
    assert classified==['mixed','all-bad','safe','inconsistent']
    # Support and verdict can survive unchanged although neither old path does.
    e={'old0':(0,1,('not',0)),'old1':(0,1,0),'endpoint':(1,2,True)}
    B,F=build(3,[0],[2],e)
    old=F.reach[:]; path=F.witness({0:False})
    revised=dict(e)
    revised['old0']=(0,1,0)
    revised['old1']=(0,1,('not',0))
    visits=F.replace_guards({i:formula(B,g) for i,(_,_,g) in revised.items()})
    assert F.reach==old and visits==1
    assert not replay_path(revised,path,[0],[2],0)
    assert F.witness({0:False})==('old1','endpoint')
    audit(B,F,revised,3,1,[0],[2],True)
    # Guard edits are not evidence restriction. A new support path can uncover
    # an old violating edge without modifying that edge or the bad predicate.
    e={'old_bad':(1,2,0),'unreachable':(0,1,False)}
    B,F=build(3,[0],[2],e)
    assert F.violation()==0
    e['unreachable']=(0,1,True)
    assert F.replace_guards({'unreachable':1})==2
    assert F.violation()==B.atom(0)
    assert F.witness({0:True})==('unreachable','old_bad')
    audit(B,F,e,3,1,[0],[2],True)
    print('controls: impossible union trace; mixed/all-bad/safe/inconsistent; stale witness despite unchanged support; new prefix reaches old violation')

def random_campaign():
    R=Random(20261126)
    def gen(k,depth):
        if not depth or R.randrange(4)==0:
            return R.choice([True,False,*range(k)])
        if R.randrange(3)==0:
            return ('not',gen(k,depth-1))
        return (R.choice(['and','or']),gen(k,depth-1),gen(k,depth-1))
    worlds=0
    cases=0
    for _ in range(300):
        n=R.randrange(2,12);k=R.randrange(1,7)
        roots=R.sample(range(n),R.randrange(1,n+1));bad=R.sample(range(n),R.randrange(n+1))
        pairs=[(u,v) for u in range(n) for v in range(u+1,n) if R.randrange(3)==0]
        pairs.extend(p for p in pairs[:] if R.randrange(3)==0)
        e={i:(u,v,gen(k,3)) for i,(u,v) in enumerate(pairs)}
        B,F=build(n,roots,bad,e)
        for step in range(9):
            if step:
                keys=R.sample(list(e),R.randrange(min(4,len(e))+1))
                for i in keys:
                    u,v,_=e[i]
                    e[i]=u,v,gen(k,3)
                assert F.replace_guards({i:formula(B,e[i][2]) for i in keys})<=n
            worlds+=audit(B,F,e,n,k,roots,bad,gen(k,3))
            cases+=1
    print(f'random: {cases} constraint/edge versions; {worlds} checked fixed-world assignments')

def size(B,root):
    seen=set()
    def visit(v):
        if v<2 or v in seen: return
        seen.add(v)
        _,a,b=B.nodes[v];visit(a);visit(b)
    visit(root)
    return len(seen)

def equality(n,interleaved):
    E=[]
    for i in range(n):
        x,y=(2*i,2*i+1) if interleaved else (i,n+i)
        E.append(('or',('and',x,y),('and',('not',x),('not',y))))
    return ('and',*E)

def scaling():
    for k in (2,4,8,12,24,48,96):
        n=k+1
        e={(j,c):(j,j+1,j if c else ('not',j)) for j in range(k) for c in range(2)}
        B,F=build(n,[0],[k],e)
        assert F.violation()==1 and len(B.nodes)==2+2*k
        r0=(0,0); prior=F.witness({i:False for i in range(k)})
        assert len(prior)==k and replay_path(e,prior,[0],[k],0)
        if k<=8:
            ps=set()
            for a in range(1<<k):
                p=F.witness({i:bool(a>>i&1) for i in range(k)})
                assert replay_path(e,p,[0],[k],a)
                ps.add(p)
            assert len(ps)==1<<k
        del_guard=F.replace_guards({r0:0})
        assert del_guard==k and F.violation()==B.atom(0)
        print(f'diamond {k:2}: guards={len(e):3} BDD arena nodes={len(B.nodes)-2:3} flat concrete paths={1<<k} deletion rows={del_guard}')
    for k in (2,4,8,10,12):
        stats=[]
        for inter in (True,False):
            B=BDD()
            i=formula(B,equality(k,inter))
            stats.append((size(B,i),len(B.nodes)-2))
        assert stats[0][0]==3*k and stats[1][0]==3*(2**k)-3
        print(f'equality {k:2}: interleaved live/arena={stats[0]} grouped live/arena={stats[1]}')

def sparse():
    # Separate clean progress chain. Only reached states, not the presence
    # of a syntactically edited guard, determine the downstream work.
    n=1027
    e={'prior':(0,1,0),'primary':(1,2,('not',0))}
    e.update({i:(i,i+1,True) for i in range(3,n-1)})
    roots=[0,3];bad=[2,n-1]
    B,F=build(n,roots,bad,e)
    initial=F.reach[:]
    assert F.violation()==1   # The second root's long branch is reachable.
    e['primary']=(1,2,True)
    m=F.replace_guards({'primary':1})
    fresh,G=build(n,roots,bad,e)
    assert m==1 and F.reach[2]!=initial[2]
    assert F.reach[3:]==initial[3:]
    assert [tape(B,i,1) for i in F.reach]==[tape(fresh,i,1) for i in G.reach]
    assert F.violation()==1   # Same final verdict, changed bad root coverage.
    print(f'sparse edit: {m} recomputed node versus {n} in fresh symbolic pass; same final verdict')

if __name__=='__main__':
    controls();random_campaign();scaling();sparse()
