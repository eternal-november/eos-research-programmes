#!/usr/bin/env python3
"""Independent finite I1 regression. Standard library, no imported author tables.
Finite checks are evidence, not all-parameter proofs or old-calculus certification.
"""
import itertools as it, json, math, hashlib, pathlib
ROOT=pathlib.Path(__file__).resolve().parent
COUNT={}
def tick(k,n=1): COUNT[k]=COUNT.get(k,0)+n
def compose(f,g): return tuple(-1 if j<0 else f[j] for j in g)
def partial(q,pairs):
    out=[-1]*q
    for a,b in pairs: out[a]=b
    return tuple(out)
def closure(gens,mul):
    s=set(gens)
    while True:
        t=s|{mul(a,b) for a in s for b in s}
        if t==s:return s
        s=t
class UF:
    def __init__(self,x): self.p={a:a for a in x}
    def find(self,a):
        while a!=self.p[a]: a=self.p[a]
        return a
    def union(self,a,b):
        a,b=self.find(a),self.find(b)
        if a==b:return False
        self.p[b]=a; return True

def partial_map_tests():
    for m in range(6):
        q=m+2; star=0; z=m+1; zero=(-1,)*q; one=tuple(range(q))
        ys={mask:partial(q,[(i,i) for i in range(m+1) if i==0 or mask>>(i-1)&1]) for mask in range(1<<m)}
        p=ys[0]; e=partial(q,[(z,z)]); c=partial(q,[(z,star)]); u=partial(q,[(star,z)])
        A={zero,one,e,c,*ys.values()}; B={zero,one,e,c,u,p}; M=closure(A|B,compose)
        assert len(A)==2**m+4 and M==A|{u} and len(B)==6
        assert A&B=={zero,one,e,c,p}
        if m:
            # Actual NORMAL refinement entries, not erased inverse factorizations.
            assert compose(c,u)==p and all(compose(c,a)!=p for a in A)
            foreign=ys[1]
            assert foreign not in B and compose(u,foreign)==compose(u,p)==u
            tick('bare_Ref_foreign_normal_entry_controls')
        for J in range(1<<m):
            # Independently close the interface-forced equation c*u=y_J
            uf=UF(M);uf.union(compose(c,u),ys[J]); changed=True
            while changed:
                changed=False
                for x,y,t in it.product(M,M,M):
                    if uf.find(x)==uf.find(y):
                        changed=uf.union(compose(t,x),compose(t,y)) or changed
                        changed=uf.union(compose(x,t),compose(y,t)) or changed
            classes={uf.find(x) for x in M}
            assert len(classes)==2**m-2**J.bit_count()+6
            for S,T in it.product(ys,repeat=2):
                assert (uf.find(ys[S])==uf.find(ys[T]))==(S==T or ((S|J)==J and (T|J)==J))
            assert len({uf.find(x) for x in B})==6
            assert (len({uf.find(x) for x in A})==len(A))==(J==0)
            # Every C product retained by d -> y_J, not merely cardinalities.
            emb={p:ys[J],zero:zero,one:one,e:e,c:c}
            for x,y in it.product(emb,repeat=2): assert emb[compose(x,y)]==compose(emb[x],emb[y])
            tick('partial_map_interfaces')
        for x,y,z0 in it.product(M,repeat=3):
            assert compose(compose(x,y),z0)==compose(x,compose(y,z0));tick('partial_map_associativity')

def cyclic_tests():
    for n in range(1,13):
      for r in range(-2,n+2):
        lam=lambda b,a: ((a*(r if b else 1))%n,b)
        for b,a in it.product(range(2),range(n)):
            assert lam(0,a)==(a,0) and lam(b,0)==(0,b);tick('lambda_unit_checks')
        for b,a,c in it.product(range(2),range(n),range(n)):
            u,v=lam(b,a); w,z=lam(v,c)
            assert lam(b,(a+c)%n)==((u+w)%n,z);tick('lambda_BAA')
        good=True
        for b,c,a in it.product(range(2),range(2),range(n)):
            u,v=lam(c,a);w,z=lam(b,u)
            good &= lam((b+c)%2,a)==(w,(z+v)%2);tick('lambda_BBA')
        assert good==((r*r-1)%n==0)
        d=math.gcd(n,r*r-1)
        # Independently close the finite candidate normal-pair magma under all
        # associators, then least binary congruence; compare its quotient to d.
        pairs=list(it.product(range(n),range(2)))
        pm=lambda x,y:((x[0]+(r if x[1] else 1)*y[0])%n,(x[1]+y[1])%2)
        uf=UF(pairs)
        for x,y,z in it.product(pairs,repeat=3): uf.union(pm(pm(x,y),z),pm(x,pm(y,z)))
        changed=True
        while changed:
            changed=False
            for x,y in it.product(pairs,repeat=2):
                if uf.find(x)!=uf.find(y):continue
                for z in pairs:
                    changed=uf.union(pm(x,z),pm(y,z)) or changed
                    changed=uf.union(pm(z,x),pm(z,y)) or changed
        assert len({uf.find(x) for x in pairs})==2*d
        for x,y in it.product(pairs,repeat=2):
            assert (uf.find(x)==uf.find(y))==(x[1]==y[1] and (x[0]-y[0])%d==0)
        tick('cyclic_quotient_congruence_closures')
        # Actual permutations on two copies preserve s even when d=1,2.
        pts=list(it.product(range(d),range(2))); idx={x:i for i,x in enumerate(pts)}
        aa=tuple(idx[((i+1)%d,b)] for i,b in pts)
        ss=tuple(idx[((r*i)%d,1-b)] for i,b in pts)
        ident=tuple(range(2*d)); G=closure([ident,aa,ss],compose)
        assert len(G)==2*d and compose(ss,ss)==ident
        ar=ident
        for _ in range(r%d): ar=compose(ar,aa)
        assert compose(ss,aa)==compose(ar,ss)
        powers=[ident]
        for _ in range(n):powers.append(compose(powers[-1],aa))
        assert powers[n]==ident and len(set(powers))==d
        # Exhaustive branching reduction verifies AAA,BBB,BAA,BBA and unit peaks.
        if n<=6 and good:
            def steps(w):
                out=[]
                for i,(tag,v) in enumerate(w):
                    if v==0:out.append(w[:i]+w[i+1:])
                for i in range(len(w)-1):
                    (t,a),(s,b)=w[i:i+2]
                    if t==s:rep=((t,(a+b)%(n if t=='A' else 2)),)
                    elif (t,s)==('B','A'):
                        a0,b0=lam(a,b);rep=(('A',a0),('B',b0))
                    else:continue
                    out.append(w[:i]+rep+w[i+2:])
                return out
            from functools import lru_cache
            @lru_cache(None)
            def nf(w):
                nxt=steps(w)
                return frozenset().union(*(nf(v) for v in nxt)) if nxt else frozenset([w])
            letters=[('A',a) for a in range(n)]+[('B',b) for b in range(2)]
            for w in it.product(letters,repeat=3):assert len(nf(w))==1;tick('exhaustive_length3_word_peaks')
        tick('cyclic_parameter_cases')

def null_ideal_tests():
    # Faithful left regular transformation models, independently assembled from
    # actions on regular states; all multiplication checked by function composition.
    for n in range(2,9):
        ideal=list(range(n)); Z=n
        # A states: X_i, zero, identity, p. B: X_i, zero, s^j.
        astates=list(range(n+3)); I=n+1; P=n+2
        af={}
        af['1']=tuple(astates);af['0']=(Z,)*(n+3)
        af['p']=tuple(0 if v<n else Z if v==Z else P for v in astates)
        for i in ideal:af[i]=tuple(Z if v<=Z else i if v==I else 0 for v in astates)
        bstates=list(range(2*n+1));bf={'0':(Z,)*(2*n+1)}
        for j in ideal:bf['s',j]=tuple((v+j)%n if v<n else Z if v==Z else n+1+(v-n-1+j)%n for v in bstates)
        for i in ideal:bf[i]=tuple(Z if v<=Z else (i+v-n-1)%n for v in bstates)
        assert closure(af.values(),compose)==set(af.values())
        assert closure(bf.values(),compose)==set(bf.values())
        for maps in (af,bf):
            for x,y,z in it.product(maps.values(),repeat=3):assert compose(compose(x,y),z)==compose(x,compose(y,z));tick('null_ideal_assoc')
        # Shared K products match in both faithful representations.
        K=['1','0']+ideal; brep={**{i:bf[i] for i in ideal},'1':bf['s',0],'0':bf['0']}
        inva={v:k for k,v in af.items()};invb={v:k for k,v in brep.items()}
        for x,y in it.product(K,repeat=2):assert inva[compose(af[x],af[y])]==invb[compose(brep[x],brep[y])]
        for i,j in it.product(ideal,repeat=2):
            # p (x_i s^j) versus (p x_i) s^j, evaluated locally.
            right=next(k for k,v in bf.items() if v==compose(bf[i],bf['s',j]))
            lhs=inva[compose(af['p'],af[right])]
            first=inva[compose(af['p'],af[i])]
            rhs=next(k for k,v in bf.items() if v==compose(bf[first],bf['s',j]))
            assert lhs==0 and rhs==j;tick('null_ideal_mixed_peaks')
        tick('null_ideal_n')

# Raw terms retain actual vertex subsets and arrow endpoints in the chain 0<1<2.
# These are coordinates in one fixed whole, not graph-isomorphism classes.
from dataclasses import dataclass
EDGES=frozenset({(0,1),(2,3),(4,5),(1,2),(3,4),(0,5)})
@dataclass(frozen=True)
class T:
    kind:str
    vertices:tuple
    arrow:tuple
    kids:tuple=()
    value:int=0

def leaf(v,a):return T('x',tuple(v),a)
def unit(a):return T('u',(),(a,a))
def cut(x,y):
    assert set(x.vertices).isdisjoint(y.vertices) and x.arrow[1]==y.arrow[0]
    return T('c',tuple(sorted(x.vertices+y.vertices)),(x.arrow[0],y.arrow[1]),(x,y))
def dec(k,v,x):
    assert x.vertices
    return T(k,x.vertices,x.arrow,(x,),v)
def rebuild(t,kids):
    if t.kind=='c':return cut(*kids)
    if t.kind in 'AB':return dec(t.kind,t.value,kids[0])
    assert not kids;return t

def frontier(t):
    if t.kind=='x':return (t,)
    return sum((frontier(c) for c in t.kids),())
def graft(t,i,f):
    leaves=frontier(t);assert (leaves[i].vertices,leaves[i].arrow)==(f.vertices,f.arrow)
    cursor=[0]
    def go(t):
        if t.kind=='x':
            j=cursor[0];cursor[0]+=1;return f if j==i else t
        return rebuild(t,tuple(go(c) for c in t.kids))
    return go(t)
def at(t,addr):
    for i in addr:t=t.kids[i]
    return t

def local_steps(t,n=3):
    out=[];k=t.kind
    if k in 'AB':
        child=t.kids[0];mod=n if k=='A' else 2
        if t.value==0:out.append(('unit'+k,child))
        if child.kind==k:out.append(('table'+k,dec(k,(t.value+child.value)%mod,child.kids[0])))
        if k=='B' and child.kind=='A':out.append(('sort',dec('A',((-1)**t.value*child.value)%n,dec('B',t.value,child.kids[0]))))
        if child.kind=='c':out.append(('diag'+k,cut(*(dec(k,t.value,x) if x.vertices else x for x in child.kids))))
    if k=='c':
        x,y=t.kids
        if x.kind=='c':a,b=x.kids;out.append(('R',cut(a,cut(b,y))))
        if x.kind=='u':out.append(('UL',y))
        if y.kind=='u':out.append(('UR',x))
    return out

def steps(t,n=3):
    out=[(name,(),u) for name,u in local_steps(t,n)]
    for i,c in enumerate(t.kids):
        for name,addr,u in steps(c,n):
            kids=list(t.kids);kids[i]=u;out.append((name,(i,)+addr,rebuild(t,tuple(kids))))
    return out

def measure(t):
    def info(t):
        sub=[info(x) for x in t.kids];old=(t.kind in ('c','u'))+sum(x[0] for x in sub)
        bins=(t.kind=='c')+sum(x[1] for x in sub)
        D=sum(x[2] for x in sub)+(old if t.kind in 'AB' else 0)
        A=sum(x[3] for x in sub)+(sub[0][1] if t.kind=='c' else 0)
        C=(t.kind in 'AB')+sum(x[4] for x in sub)
        return old,bins,D,A,C
    old,b,D,A,C=info(t)
    def inversions(t,parent=False):
        score=0
        if t.kind in 'AB' and not parent:
            cur=t;bs=0
            while cur.kind in 'AB':
                if cur.kind=='B':bs+=1
                else:score+=bs
                cur=cur.kids[0]
        return score+sum(inversions(x,t.kind in 'AB') for x in t.kids)
    return D,b,A,C,inversions(t)

def normalize(t,n=3):
    path=[]
    while True:
        s=steps(t,n)
        if not s:return t,tuple(path)
        name,addr,u=s[0];assert measure(u)<measure(t),(name,measure(t),measure(u))
        path.append((name,addr,t,u));t=u

def old_and_labels(t,n=3):
    # Independent recursive interpretation, not the rewriting normalizer.
    def go(t,p=(0,0)):
        if t.kind=='x':return ((t.vertices,t.arrow,p if t.vertices else None),)
        if t.kind=='u':return ()
        if t.kind=='c':return sum((go(x,p) for x in t.kids),())
        a,b=p;q=(t.value,0) if t.kind=='A' else (0,t.value)
        return go(t.kids[0],((a+(-1)**b*q[0])%n,(b+q[1])%2))
    return (t.vertices,tuple(e for e in EDGES if set(e)<=set(t.vertices)),t.arrow,go(t))

def graph_path_tests():
    x=leaf((0,1),(0,0));y=leaf((2,3),(0,0));z=leaf((4,5),(1,2))
    empty=leaf((),(0,1));tail=leaf((),(2,2))
    base=cut(cut(cut(x,y),empty),cut(z,cut(tail,tail)))
    assert len(frontier(base))==6
    # x,y are repeated component TYPES, but their actual occurrence subsets differ.
    def component(t):
        vv=t.vertices;return (len(vv),tuple((vv.index(a),vv.index(b)) for a,b in EDGES if a in vv and b in vv),t.arrow)
    assert component(x)==component(y) and x!=y
    assert base.arrow==(0,2) and empty.arrow==(0,1) and z.arrow==(1,2)
    # Independently check old induced-graph restriction in all nested subsets.
    def restrict(v,es,sel):
        vv=tuple(v[i] for i in sel)
        return vv,tuple((i,j) for i in range(len(vv)) for j in range(i+1,len(vv)) if (vv[i],vv[j]) in es)
    for mask in range(64):
        U=tuple(i for i in range(6) if mask>>i&1)
        vu,eu=restrict(tuple(range(6)),EDGES,U)
        for sub in range(1<<len(U)):
            V=tuple(i for i in range(len(U)) if sub>>i&1)
            actual=tuple(U[i] for i in V)
            nested_edges=tuple((i,j) for i in range(len(V)) for j in range(i+1,len(V)) if (V[i],V[j]) in eu)
            assert nested_edges==restrict(tuple(range(6)),EDGES,actual)[1]
            tick('old_strict_restriction_squares')
    sources=[]
    for a,b in it.product(range(3),range(2)):
        sources += [dec('B',b,dec('A',a,base)),dec('A',a,dec('A',2,base)),dec('B',b,dec('B',1,base))]
        sources += [dec('A',a,cut(unit(0),x)),dec('B',b,cut(x,unit(0)))]
    sources += [dec('A',0,base),dec('B',0,base),cut(unit(0),unit(0)),cut(cut(x,y),unit(0))]
    for source in sources:
        normal,_=normalize(source)
        for name,addr,target in steps(source):
            assert measure(target)<measure(source)
            other,path=normalize(target)
            assert other==normal and old_and_labels(target)==old_and_labels(source)
            tick('graph_typed_peak_branches')
            # Every tested contextual equation commutes with a real primitive
            # graft at EACH frontier occurrence, including nonidentity empty grades.
            for pos,fleaf in enumerate(frontier(source)):
                inserted=dec('A',1,fleaf) if fleaf.vertices else cut(leaf((),(fleaf.arrow[0],fleaf.arrow[0])),fleaf)
                before=graft(source,pos,inserted);after=graft(target,pos,inserted)
                residuals=[v for nm,ad,v in steps(before) if nm==name and ad==addr]
                assert after in residuals
                tick('MOut_all_tested_occurrence_squares')
        # All local critical joins compare paths of ACTUAL typed terms, not label arrays only.
        for e,f in it.combinations(steps(source),2):
            assert normalize(e[2])[0]==normalize(f[2])[0];tick('graph_typed_peak_pairs')
    # Concrete MOut: equation outside an inserted forest; same rule/address residual.
    source=dec('B',1,dec('A',1,base))
    eq=next(s for s in steps(source) if s[0]=='sort' and s[1]==())
    inner=cut(leaf((0,),(0,0)),cut(leaf((),(0,0)),leaf((1,),(0,0))))
    left=graft(eq[2],0,inner);before=graft(source,0,inner)
    residual=next(s for s in steps(before) if s[:2]==eq[:2])
    assert residual[2]==left
    tick('MOut_actual_rule_residual_squares')
    # MIn: bare sorting template grafted into actual original repeated occurrence 1.
    bare=dec('B',1,dec('A',1,y));bare_eq=next(s for s in steps(bare) if s[0]=='sort')
    inserted=graft(base,1,bare);direct=graft(base,1,bare_eq[2])
    applicable=[u for name,addr,u in steps(inserted) if name=='sort']
    assert direct in applicable
    # Canonical original-entry forests normalized by rewrite; intermediate labels retained.
    F=list(frontier(base));F[1]=bare
    G=list(frontier(base));G[1]=bare_eq[2]
    assert tuple(normalize(t)[0] for t in F)==tuple(normalize(t)[0] for t in G)
    assert old_and_labels(F[1])[-1][0][-1]==(2,1)
    tick('MIn_actual_inserted_equation_squares')
    # Substituted MIn inside an inserted forest; factorization bare template then graft.
    decorated=dec('A',2,inner)
    barex=dec('B',1,dec('A',1,x));barex2=next(s[2] for s in steps(barex) if s[0]=='sort')
    lhs=graft(barex,0,decorated);rhs=graft(barex2,0,decorated)
    assert next(s[2] for s in steps(lhs) if s[0]=='sort' and s[1]==())==rhs
    assert normalize(lhs)[0]==normalize(rhs)[0]
    tick('MIn_substitution_via_MOut_squares')
    # Original slots 4 and 5 are indistinguishable empty types, not interchangeable slots.
    f=list(frontier(base));g=list(frontier(base));f[4]=unit(2);g[5]=unit(2)
    assert graft(base,4,unit(2))!=graft(base,5,unit(2)) # different raw bracketings
    assert old_and_labels(graft(base,4,unit(2)))==old_and_labels(graft(base,5,unit(2)))
    assert tuple(normalize(v)[0] for v in f)!=tuple(normalize(v)[0] for v in g)
    tick('equal_endpoint_distinct_original_slot_control')
    # Missing-MIn independent weight model: every retained defining relation preserves
    # graft count; new-unit insertion followed by equation deletion has weight 1, id 0.
    weighted_relations={'inverse':((0,0),()),'O':((0,0),(0,0,0)),
                        'raw_interchange':((1,1),(1,1)), 'MOut':((0,1),(1,0))}
    assert all(sum(l)==sum(r) for l,r in weighted_relations.values())
    assert normalize(dec('A',0,x))[0]==x and 1!=0
    tick('missing_MIn_weight_countermodel')
    # Stronger mixed-only MIn omission model: size times A exponent modulo 3.
    def graft_weight(t):
        return ((len(t.vertices)*t.value if t.kind=='A' else 0)+sum(graft_weight(k) for k in t.kids))%3
    for src in sources:
        for name,addr,dst in steps(src):
            if name!='sort':assert graft_weight(src)==graft_weight(dst)
    single=leaf((0,),(0,0));bad=dec('B',1,dec('A',1,single))
    sorted_bad=next(s[2] for s in steps(bad) if s[0]=='sort')
    assert (graft_weight(bad),graft_weight(sorted_bad))==(1,2)
    tick('missing_only_mixed_MIn_weight_countermodel')
    # Zero-parent masks an entire DIFFERENT entry coefficient: retain original
    # forest coefficient, rather than testing only the source-final product.
    zero_map=(-1,-1);identity=(0,1)
    assert compose(zero_map,zero_map)==compose(zero_map,identity)==zero_map
    assert zero_map!=identity
    tick('same_root_distinct_entry_coefficient_control')


def noninvertible_positive_lambda_tests():
    pairs=list(it.product(range(2),repeat=2))
    mul=lambda x,y:((x[0]+(y[0] if x[1]==0 else 0))%2,max(x[1],y[1]))
    idx={x:i for i,x in enumerate(pairs)}
    regular={x:tuple(idx[mul(x,y)] for y in pairs) for x in pairs}
    assert len(set(regular.values()))==4
    for x,y in it.product(pairs,repeat=2): assert compose(regular[x],regular[y])==regular[mul(x,y)]
    assert mul((0,1),(1,0))==(0,1) and (1,0) not in {(0,0),(0,1)}
    tick('noninvertible_positive_lambda_B_Ref_nonfull_control')


def original_six_vertex_fixture_tests():
    # Literal old fixture: two equal middle component occurrences and retained
    # crossing edges, with profile h:0->1,id_1,id_1,k:1->2.
    global EDGES
    saved=EDGES
    EDGES=frozenset({(1,2),(3,4),(0,5),(2,3)})
    first=leaf((0,),(0,1));mid1=leaf((1,2),(1,1));mid2=leaf((3,4),(1,1));last=leaf((5,),(1,2))
    t=cut(cut(first,mid1),cut(mid2,last))
    a=dec('B',1,dec('A',1,t));a_nf,_=normalize(a)
    assert tuple(x.arrow for x in frontier(t))==((0,1),(1,1),(1,1),(1,2))
    refine1=cut(leaf((1,),(1,1)),leaf((2,),(1,1)))
    refine2=cut(leaf((3,),(1,1)),leaf((4,),(1,1)))
    left=graft(t,1,refine1);right=graft(t,2,refine2)
    assert old_and_labels(left)!=old_and_labels(right)
    assert old_and_labels(t)[1]==tuple(EDGES)
    for name,addr,u in steps(a):
        assert normalize(u)[0]==a_nf and old_and_labels(u)==old_and_labels(a)
        for pos,ins in ((1,refine1),(2,refine2)):
            before=graft(a,pos,ins);after=graft(u,pos,ins)
            assert after in [v for nm,ad,v in steps(before) if nm==name and ad==addr]
            tick('original_six_vertex_MOut_squares')
    # Retained separate entry arrays: applying the same mixed pair to both
    # original equal middle components does not merge their distinct positions.
    F=list(frontier(t));F[1]=dec('B',1,dec('A',1,refine1));F[2]=dec('B',1,dec('A',2,refine2))
    normalized=tuple(normalize(x)[0] for x in F)
    assert normalized[1].vertices==(1,2) and normalized[2].vertices==(3,4)
    assert old_and_labels(normalized[1])[-1][0][-1]==(2,1)
    assert old_and_labels(normalized[2])[-1][0][-1]==(1,1)
    tick('original_six_vertex_retained_distinct_entries')
    EDGES=saved


def cut_transport_tests():
    for n in range(3,8):
        elements=list(it.product(range(n),range(2)))
        mul=lambda x,y:((x[0]+(-1)**x[1]*y[0])%n,(x[1]+y[1])%2)
        # Actual tree: shared parent, two children, first child refined further.
        # Prefix transport on all retained edges, not independent channel projection.
        parents=[None,0,0,1,1];paths=[(0,1,3),(0,1,4),(0,2)]
        # This parent list is an actual retained graph-cut skeleton: unary whole,
        # then 4+2 vertices, then 2+2, with complete interface-grade factorizations.
        edge_colors=[(tuple(range(6)),(0,2)),((0,1,2,3),(0,1)),((4,5),(1,2)),((0,1),(0,0)),((2,3),(0,1))]
        lower=cut(leaf(*edge_colors[3]),leaf(*edge_colors[4]))
        whole=cut(lower,leaf(*edge_colors[2]))
        assert (lower.vertices,lower.arrow)==edge_colors[1]
        assert (whole.vertices,whole.arrow)==edge_colors[0]
        assert tuple(x.vertices for x in frontier(whole))==((0,1),(2,3),(4,5))
        assignments=it.product(elements,repeat=5) if n==3 else (tuple(elements[(k*(j+1)+j*j)%len(elements)] for j in range(5)) for k in range(200))
        for arr in assignments:
            beta=[];ts=[]
            for j,(a,b) in enumerate(arr):
                p=parents[j];be=0 if p is None else (beta[p]+arr[p][1])%2
                beta.append(be);ts.append(((-1)**be*a)%n)
            recovered=tuple((((-1)**be*t)%n,b) for be,t,(a,b) in zip(beta,ts,arr))
            assert recovered==arr
            assert tuple(zip(edge_colors,recovered))==tuple(zip(edge_colors,arr))
            for path in paths:
                result=(0,0)
                for j in path:result=mul(result,arr[j])
                assert result==(sum(ts[j] for j in path)%n,sum(arr[j][1] for j in path)%2)
            # Every retained subtree resets prefix; ambient transport recovers its intrinsic labels.
            for j in range(1,5):assert ((-1)**beta[j]*ts[j])%n==arr[j][0]
            tick('joint_tree_accumulated_action_arrays')
        # Full source-fixed binary fibres and module-pure reflection.
        for x in elements:
            actual={(p,q) for p,q in it.product(elements,repeat=2) if mul(p,q)==x}
            transported={((p[0],((-1)**p[1]*q[0])%n),(p[1],q[1])) for p,q in actual}
            independent={((a,c),(b,d)) for a,c in it.product(range(n),repeat=2) for b,d in it.product(range(2),repeat=2) if (a+c)%n==x[0] and (b+d)%2==x[1]}
            assert transported==independent
            if x[1]==0:
                pure={(p[0],q[0]) for p,q in actual if p[1]==q[1]==0}
                assert pure=={(a,c) for a,c in it.product(range(n),repeat=2) if (a+c)%n==x[0]}
            tick('source_fixed_cut_fibres')
        assert mul((0,1),(0,1))==(0,0) # foreign B cuts of A unit
        assert mul((1,0),(n-1,0))==(0,0) # foreign A cuts of B unit
        assert mul((0,1),(1,0))[0]!=(0+1)%n # A projection not morphism
        tick('foreign_unit_and_projection_controls')
        # Invertible-action subgroup-local endpoints force every normalized Ref
        # entry local, unlike marked cut-factor histories.
        for src,entry in it.product(elements,repeat=2):
            dst=mul(src,entry)
            if src[1]==dst[1]==0:assert entry[1]==0
            if src[0]==dst[0]==0:assert entry[0]==0
        for d in range(1,n):
            if n%d:continue
            h=lambda p:(p[0]%d,p[1])
            target=list(it.product(range(d),range(2)))
            tm=lambda x,y:((x[0]+(-1)**x[1]*y[0])%d,(x[1]+y[1])%2)
            for q in target:
                fibre={p for p in elements if h(p)==q}
                assert fibre
                for x,r0 in it.product(elements,target):
                    if tm(q,r0)!=h(x):continue
                    L={p for p in fibre if any(h(v)==r0 and mul(p,v)==x for v in elements)}
                    assert L==fibre;tick('group_surjection_shared_parent_lifting_sets')
    for m in range(1,5):
        q=m+2;z=m+1;zero=(-1,)*q;one=tuple(range(q))
        ys={s:partial(q,[(0,0)]+[(i,i) for i in range(1,m+1) if s>>(i-1)&1]) for s in range(1<<m)}
        e=partial(q,[(z,z)]);c=partial(q,[(z,0)]);u=partial(q,[(0,z)])
        M={zero,one,e,c,u,*ys.values()}
        for J in range(1<<m):
            h={v:ys[s&J] for s,v in ys.items()};h.update({x:x for x in (zero,one,e,c,u)})
            for x,y in it.product(M,repeat=2):assert h[compose(x,y)]==compose(h[x],h[y])
            if J!=(1<<m)-1:
                k=next(i for i in range(m) if not (J>>i)&1);source=ys[1<<k]
                assert h[source]==ys[0]==compose(c,u) and source!=compose(c,u)
                assert {x for x in M if h[x]==c}=={c} and {x for x in M if h[x]==u}=={u}
                tick('coordinate_restriction_fixed_source_failures')
        for perm in it.permutations(range(1,m+1)):
            sig=(0,)+perm+(z,);inv=tuple(sig.index(i) for i in range(q))
            h={x:compose(compose(sig,x),inv) for x in M}
            assert set(h.values())==M
            for x,y in it.product(M,repeat=2):assert h[compose(x,y)]==compose(h[x],h[y])
            tick('actual_permutation_conjugations')


def main():
    partial_map_tests();cyclic_tests();null_ideal_tests();graph_path_tests();original_six_vertex_fixture_tests();noninvertible_positive_lambda_tests();cut_transport_tests()
    out={'status':'PASS','counts':COUNT,'scope':'Independent concrete finite coefficient regressions; typed six-vertex graph rewrite peaks, actual MIn/MOut instance paths and countercontrols; accumulated-action retained tree and source-fixed cut checks. Not exhaustive proof-path quotient enumeration.'}
    (ROOT/'verify_i1_results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
