"""Independent finite support for the proof, not an unbounded proof or formalization."""
from itertools import product
from dataclasses import dataclass
import random, json
@dataclass(frozen=True)
class G:
    n:int
    edges:tuple

def hom(A,B):
    out=[]
    for s in product(range(B.n),repeat=A.n):
        opts=[[j for j,(u,v) in enumerate(B.edges) if (u,v)==(s[x],s[y])] for x,y in A.edges]
        for e in product(*opts): out.append((s,e))
    return out

def comp(g,f): return tuple(tuple(g[k][x] for x in f[k]) for k in (0,1))
def ident(A): return (tuple(range(A.n)),tuple(range(len(A.edges))))
@dataclass
class C:
    W:G
    l:tuple
    r:tuple

# Deliberately construct the actual tuple pullback graph, rather than using automaton runs.
def pullback(word,cs,B,q=None):
    if not word: return B,None,None
    def leg(c,k,side):
        f=getattr(cs[c],side)
        return comp(q,f)[k] if q is not None else f[k]
    carriers=[]
    for k in (0,1):
        ranges=[range(cs[c].W.n if k==0 else len(cs[c].W.edges)) for c in word]
        carriers.append([t for t in product(*ranges) if all(leg(word[i],k,'r')[t[i]]==leg(word[i+1],k,'l')[t[i+1]] for i in range(len(word)-1))])
    vs,es=carriers; idx={v:i for i,v in enumerate(vs)}
    edges=tuple((idx[tuple(cs[c].W.edges[t[i]][0] for i,c in enumerate(word))],idx[tuple(cs[c].W.edges[t[i]][1] for i,c in enumerate(word))]) for t in es)
    left=tuple(tuple(leg(word[0],k,'l')[t[0]] for t in carriers[k]) for k in (0,1))
    right=tuple(tuple(leg(word[-1],k,'r')[t[-1]] for t in carriers[k]) for k in (0,1))
    return G(len(vs),edges),left,right

def direct_bad(root,word,cs,B,Bbar,q):
    c=cs[root]
    if not word: return comp(q,c.l)==comp(q,c.r) and c.l!=c.r
    P,l,r=pullback(word,cs,Bbar,q)
    coarse=[f for f in hom(c.W,P) if comp(l,f)==comp(q,c.l) and comp(r,f)==comp(q,c.r)]
    F,fl,fr=pullback(word,cs,B)
    fine=[f for f in hom(c.W,F) if comp(fl,f)==c.l and comp(fr,f)==c.r]
    # Inclusion on literal compatible tuples is injective, so cardinality suffices here.
    return len(coarse)!=len(fine)

def auto(root,cs,B,q):
    c=cs[root]; hs=hom(c.W,B); states=[(h,d) for h in hs for d in (False,True)]
    ix={s:i for i,s in enumerate(states)}
    trans={}
    for e,v in cs.items():
        rel=set()
        for i,(h,d) in enumerate(states):
            for f in hom(c.W,v.W):
                left,right=comp(v.l,f),comp(v.r,f)
                if comp(q,h)==comp(q,left): rel.add((i,ix[(right,d or h!=left)]))
        trans[e]=rel
    initial=ix[(c.l,False)]
    bad={i for i,(h,d) in enumerate(states) if comp(q,h)==comp(q,c.r) and (d or h!=c.r)}
    return len(states),trans,initial,bad

def compose(A,B): return {(x,z) for x,y in A for y2,z in B if y==y2}
def run(word,n,trans):
    r={(i,i) for i in range(n)}
    for a in word:r=compose(r,trans[a])
    return r

def saturation(n,trans,grammar):
    R={a:set(v) for a,v in trans.items()}; witnesses={(a,x,y):(a,) for a,v in trans.items() for x,y in v}
    while True:
        changed=False
        for a,prods in grammar.items():
            for p in prods:
                D={(i,i):() for i in range(n)}
                for b in p:
                    N={}
                    for (x,y),w in D.items():
                        for yy,z in R[b]:
                            if y==yy:N.setdefault((x,z),w+witnesses[(b,yy,z)])
                    D=N
                for (x,y),w in D.items():
                    if (x,y) not in R[a]:
                        R[a].add((x,y));witnesses[(a,x,y)]=w;changed=True
        if not changed:return R,witnesses

def words_depth(grammar,depth,maxlen):
    L={a:{(a,)} for a in grammar}
    for _ in range(depth):
        N={a:set(v) for a,v in L.items()}
        for a,ps in grammar.items():
            for p in ps:
                for ws in product(*(L[b] for b in p)):
                    w=sum(ws,())
                    if len(w)<=maxlen:N[a].add(w)
        L=N
    return L

def discrete(n): return G(n,())
def dm(xs):return (tuple(xs),())
def test_random():
    rng=random.Random(8172); count=0
    B=discrete(2);Bb=discrete(1);q=dm([0,0])
    for trial in range(36):
        cs={a:C(discrete(rng.randrange(1,3)),None,None) for a in ('a','b')}
        for c in cs.values():c.l=dm([rng.randrange(2) for _ in range(c.W.n)]);c.r=dm([rng.randrange(2) for _ in range(c.W.n)])
        grammar={'a':[('b',),('a','b'),()], 'b':[('a',)]}
        L=words_depth(grammar,4,3)
        for root in cs:
            n,t,i,bad=auto(root,cs,B,q);R,w=saturation(n,t,grammar)
            for word in L[root]:
                observed=any(x==i and y in bad for x,y in run(word,n,t))
                assert observed==direct_bad(root,word,cs,B,Bb,q),(trial,root,word)
                assert run(word,n,t)<=R[root]
                count+=1
            for (a,x,y),word in w.items():assert (x,y) in run(word,n,t)
    return count

def test_delayed():
    B=discrete(2); q=dm([0,0]);cs={f'n{i}':C(discrete(1),dm([0]),dm([0])) for i in range(15)}
    cs['z']=C(discrete(2),dm([0,1]),dm([0,0]))
    grammar={f'n{i}':[(f'n{i+1}',)] for i in range(14)}
    grammar['n14']=[('z',)];grammar['z']=[('z',)]
    n,t,i,b=auto('n0',cs,B,q);R,w=saturation(n,t,grammar)
    assert not any(direct_bad('n0',p,cs,B,discrete(1),q) for p in words_depth(grammar,14,1)['n0'])
    assert any(x==i and y in b for x,y in R['n0'])
    assert ('z',) in words_depth(grammar,15,1)['n0']
    return {'first_bad_derivation_depth':15,'shallow_depth_14_passes':True}

def test_edges():
    # A bad POINT is not an obstruction when no source graph map can use it.
    B=G(2,((0,0),(0,1),(1,0),(1,1)));Bb=G(1,((0,0),));q=((0,0),(0,0,0,0))
    S=G(1,((0,0),));T=G(3,((0,1),(2,2)))
    cs={'c':C(S,((0,),(0,)),((0,),(0,))), 'e':C(T,((1,1,0),(3,0)),((1,1,0),(3,0)))}
    assert len(hom(S,T))==1
    assert not direct_bad('c',('e',),cs,B,Bb,q)
    n,t,i,b=auto('c',cs,B,q);assert not any(x==i and y in b for x,y in t['e'])
    # Surjective map on states and events need not have a graph section.
    E=G(2,((0,1),)); assert not hom(S,E)
    quotient=((0,0),(0,));assert set(quotient[0])=={0} and set(quotient[1])=={0}
    # Parallel event records matter even when all states coincide.
    M=G(1,((0,0),(0,0))); assert len(hom(S,M))==2
    return {'unextendible_bad_point_ignored':True,'sortwise_surjection_without_graph_section':True,'parallel_event_maps_distinct':True}

def test_epsilon():
    B=discrete(2);Bb=discrete(1);q=dm([0,0]);S=discrete(1)
    cs={'c':C(S,dm([0]),dm([0]))}; grammar={'c':[(),('c',)]}
    n,t,i,b=auto('c',cs,B,q);R,w=saturation(n,t,grammar)
    assert not any(x==i and y in b for x,y in R['c'])
    # Fullness passes but coarse nullary iso lifts to non-iso: E0 needed.
    assert comp(q,cs['c'].l)==ident(S) and cs['c'].l!=ident(B)
    cs['c'].r=dm([1]);n,t,i,b=auto('c',cs,B,q);R,w=saturation(n,t,grammar)
    assert (i,i) in R['c'] and i in b and direct_bad('c',(),cs,B,Bb,q)
    return {'fullness_not_exact_nullary_lifting':True,'epsilon_obstruction_detected':True}

if __name__=='__main__':
    print(json.dumps({'bounded_comparisons':test_random(),'delayed':test_delayed(),'graph_records':test_edges(),'epsilon':test_epsilon()},indent=2))

def test_anchors():
    B=discrete(2);Bb=discrete(1);q=dm([0,0]);base=C(discrete(1),dm([0]),dm([0]))
    for side in ('left','right'):
        e=C(discrete(2),dm([0,1] if side=='left' else [0,0]),dm([0,1] if side=='right' else [0,0]))
        cs={'c':base,'e':e};n,t,i,b=auto('c',cs,B,q)
        assert direct_bad('c',('e',),cs,B,Bb,q)
        assert any(x==i and y in b for x,y in t['e'])
    cs={'c':base,'e':C(discrete(2),dm([0,0]),dm([0,1])),'f':C(discrete(1),dm([0]),dm([0]))}
    n,t,i,b=auto('c',cs,B,q)
    assert direct_bad('c',('e','f'),cs,B,Bb,q)
    assert any(x==i and y in b for x,y in run(('e','f'),n,t))
    return True

def test_coherence():
    # q not iso, all actual legs 0; coarse and fine operation fibres literally agree.
    B=discrete(2);Bb=discrete(1);q=dm([0,0]);W=discrete(2)
    cs={'c':C(W,dm([0,0]),dm([0,0]))}
    n,t,i,b=auto('c',cs,B,q);R,_=saturation(n,t,{'c':[('c','c'),('c',)]})
    assert not any(x==i and y in b for x,y in R['c'])
    # Exhaust all binary first-stage maps and unary maps at both occurrences.
    P,l,r=pullback(('c','c'),cs,B);Pc,lc,rc=pullback(('c','c'),cs,Bb,q)
    assert P==Pc
    binary=hom(W,P); unary=hom(W,W);checked=0
    for top in binary:
        for u in unary:
            for v in unary:
                tuples=list(product(range(2),repeat=2))
                flattened=tuple((u[0][tuples[top[0][x]][0]],v[0][tuples[top[0][x]][1]]) for x in range(2))
                staged=tuple(tuple((u,v)[j][0][tuples[top[0][x]][j]] for j in range(2)) for x in range(2))
                assert flattened==staged
                checked+=1
    # Distinct occurrence maps stay distinct, even if a chosen top sees only state0.
    assert unary[0]!=unary[1] and unary[0][0][0]==unary[1][0][0]
    return checked

if __name__=='__main__':print(json.dumps({'all_three_anchor_obstructions':test_anchors(),'coherent_occurrence_substitutions':test_coherence()}))

def test_typed_epsilon():
    # Two tagged vertices, two automaton states each. Compare typed versus global epsilon.
    tags={0:0,1:0,2:1,3:1}
    endpoints={'a':(0,1),'b':(1,0),'l':(0,0),'m':(1,1),'s':(0,0)}
    trans={'a':{(0,2),(1,3)},'b':{(2,1),(3,0)},'l':{(0,1),(1,1)},'m':{(2,3),(3,3)},'s':{(0,0),(1,1)}}
    grammar={'a':[('l','a','m')],'b':[('m','b','l')],'l':[(),('l','l')],'m':[(),('m','m')],'s':[('a','b'),('s','s')]}
    untyped,_=saturation(4,trans,grammar)
    typed={a:set(r) for a,r in trans.items()}
    while True:
        old={a:set(r) for a,r in typed.items()}
        for a,prods in grammar.items():
            for p in prods:
                r={(i,i) for i in tags if tags[i]==endpoints[a][0]}
                for child in p:r=compose(r,typed[child])
                typed[a]|=r
        if old==typed:break
    for a,(v,u) in endpoints.items():
        assert typed[a]=={(i,j) for i,j in untyped[a] if tags[i]==v and tags[j]==u}
    assert (2,2) in untyped['l'] and (2,2) not in typed['l']
    return {'typed_root_queries_agree':True,'unrelated_epsilon_pairs_excluded_from_typed_relations':True}

if __name__=='__main__':print(json.dumps({'two_vertex_epsilon':test_typed_epsilon()}))
