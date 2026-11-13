#!/usr/bin/env python3
"""Independent global-incidence representation; never imports author sources."""
from dataclasses import dataclass,replace
from itertools import product,combinations,combinations_with_replacement
from collections import Counter,defaultdict
from pathlib import Path
from math import comb
import hashlib,json,time
P=Path(__file__).parent
COUNT=Counter(); TRACE=hashlib.sha256()
TABLES={'Z3':((0,1,2),(1,2,0),(2,0,1)),'E2':((0,1),(1,1)),'One':((0,),)}
@dataclass(frozen=True)
class Tree:
    tag:str; vertices:tuple; edges:tuple; arrow:tuple; children:tuple=(); value:int=0

def restrict_edges(E,V):return tuple(e for e in E if e[0] in V and e[1] in V)
def leaf(V,E,a):return Tree('l',tuple(V),restrict_edges(E,V),a)
def unit(a):return Tree('u',(),(),(a,a,0))
def val(v,t):return replace(t,tag='d',children=(t,),value=v)
def cut(x,y,E):
    assert x.arrow[1]==y.arrow[0] and not set(x.vertices)&set(y.vertices)
    V=tuple(sorted(x.vertices+y.vertices));E=restrict_edges(E,V)
    assert x.edges==restrict_edges(E,x.vertices) and y.edges==restrict_edges(E,y.vertices)
    return Tree('c',V,E,(x.arrow[0],y.arrow[1],x.arrow[2]^y.arrow[2]),(x,y))
def occurrences(t):
    if t.tag=='l':return [((),t)]
    return [( (i,)+a,l) for i,c in enumerate(t.children) for a,l in occurrences(c)]
def graft(t,F):
    leaves=occurrences(t);assert len(leaves)==len(F)
    for (_,l),f in zip(leaves,F):assert (l.vertices,l.edges,l.arrow)==(f.vertices,f.edges,f.arrow)
    assignments=dict(zip((a for a,l in leaves),F))
    def go(t,a):return assignments[a] if t.tag=='l' else replace(t,children=tuple(go(c,a+(i,)) for i,c in enumerate(t.children)))
    return go(t,())
def get(t,a):
    for i in a:t=t.children[i]
    return t

def alter(t,a,q):
    if not a:return q
    cs=list(t.children);cs[a[0]]=alter(cs[a[0]],a[1:],q);return replace(t,children=tuple(cs))
def rewrite(t,a,r,M):
    x=get(t,a);cs=x.children
    if r=='D0':assert x.tag=='d' and x.value==0;y=cs[0]
    elif r=='DA':
        assert x.tag=='d' and cs[0].tag=='d';y=val(M[x.value][cs[0].value],cs[0].children[0])
    elif r=='UL':assert x.tag=='c' and cs[0].tag=='u';y=cs[1]
    elif r=='UR':assert x.tag=='c' and cs[1].tag=='u';y=cs[0]
    elif r=='DL':assert x.tag=='c' and cs[0].tag=='d';y=val(cs[0].value,cut(cs[0].children[0],cs[1],x.edges))
    elif r=='DR':assert x.tag=='c' and cs[1].tag=='d';y=val(cs[1].value,cut(cs[0],cs[1].children[0],x.edges))
    else:
        assert r=='R' and x.tag=='c' and cs[0].tag=='c'
        l,m=cs[0].children;y=cut(l,cut(m,cs[1],x.edges),x.edges)
    assert (x.vertices,x.edges,x.arrow)==(y.vertices,y.edges,y.arrow)
    return alter(t,a,y)
def redexes(t):
    out=[]
    if t.tag=='d':
        if t.value==0:out.append(((),'D0'))
        if t.children[0].tag=='d':out.append(((),'DA'))
    if t.tag=='c':
        x,y=t.children
        for b,r in ((x.tag=='u','UL'),(y.tag=='u','UR'),(x.tag=='d','DL'),(y.tag=='d','DR'),(x.tag=='c','R')):
            if b:out.append(((),r))
    for i,c in enumerate(t.children):out += [((i,)+a,r) for a,r in redexes(c)]
    return out

def normal(t,M):
    trace=[]
    while (rs:=redexes(t)):
        a,r=rs[0];t=rewrite(t,a,r,M);trace.append((a,r))
    return t,tuple(trace)

def flat(t,M):
    # Explicit stack preorder; aggregation is not the rewrite normalizer.
    todo=[t];blocks=[];arrows=[];value=0
    while todo:
        q=todo.pop()
        if q.tag=='l':blocks.append(q.vertices);arrows.append(q.arrow)
        elif q.tag=='d':value=M[value][q.value];todo.extend(q.children)
        else:todo.extend(reversed(q.children))
    return (t.vertices,t.edges,t.arrow,tuple(blocks),tuple(arrows),value)
def compose(w,es,M):
    V,E,a,bs,ars,v=w;assert len(es)==len(bs)
    out=[];outar=[]
    for B,ar,e in zip(bs,ars,es):
        assert e[:3]==(B,restrict_edges(E,B),ar)
        out.extend(e[3]);outar.extend(e[4]);v=M[v][e[5]]
    return V,E,a,tuple(out),tuple(outar),v

def canonical(w):
    V,E,a,bs,ars,v=w
    def build(i):
        if i==len(bs):return unit(a[0])
        l=leaf(bs[i],E,ars[i])
        return l if i+1==len(bs) else cut(l,build(i+1),E)
    q=build(0);return val(v,q) if v else q

def pc(a,b):return ('c',a,b)
def pd(v,x):return ('d',v,x)
SHAPES=[pc(pc('x','y'),'u'),pc(pc('x','y'),pd('m','z')),pc('u','u'),pc('u',pd('m','x')),pc(pd('m','x'),'u'),pc(pd('m','x'),pd('n','y')),pd(0,pd('n','x')),pc(pc(pc('x','y'),'z'),'w'),pc(pc('u','x'),'y'),pc(pc('x','u'),'y'),pc(pc(pd('m','x'),'y'),'z'),pc(pc('x',pd('m','y')),'z'),pd('m',pd('n',pd('p','x'))),pd('m',pd(0,'x')),pc(pd('m',pd('n','x')),'y'),pc(pd(0,'x'),'y'),pc('x',pd('m',pd('n','y'))),pc('x',pd(0,'y'))]
BARE=[('R',pc(pc('x','y'),'z')),('UL',pc('u','x')),('UR',pc('x','u')),('D0',pd(0,'x')),('DA',pd('m',pd('n','x'))),('DL',pc(pd('m','x'),'y')),('DR',pc('x',pd('m','y')))]
JOINS=[('R@,UR@R','UR@'),('R@,DR@R,DR@','DR@,R@D'),('UL@','UR@'),('UL@','DR@,UL@D'),('UR@','DL@,UR@D'),('DL@,DR@D,DA@','DR@,DL@D,DA@'),('D0@','DA@'),('R@,R@','R@L,R@,R@R'),('R@,UL@','UL@L'),('R@,UL@R','UR@L'),('R@,DL@','DL@L,DL@,R@D'),('R@,DL@R,DR@','DR@L,DL@,R@D'),('DA@,DA@','DA@D,DA@'),('DA@','D0@D'),('DL@,DL@D,DA@','DA@L,DL@'),('DL@,D0@','D0@L'),('DR@,DR@D,DA@','DA@R,DR@'),('DR@,D0@','D0@R')]
def parameters(p):
    if isinstance(p,str):return (0 if p=='u' else 1),set()
    if p[0]=='d':
        n,s=parameters(p[2]);return n,s|({p[1]} if isinstance(p[1],str) else set())
    n,s=parameters(p[1]);m,t=parameters(p[2]);return n+m,s|t

def instance(p,V,E,bs,objs,zs,labels):
    i=0
    def go(p):
        nonlocal i
        if p=='u':return unit(objs[i])
        if isinstance(p,str):
            q=leaf(bs[i],E,(objs[i],objs[i+1],zs[i]));i+=1;return q
        if p[0]=='d':return val(labels[p[1]] if isinstance(p[1],str) else p[1],go(p[2]))
        return cut(go(p[1]),go(p[2]),E)
    t=go(p);assert t.vertices==V;return t

def join(t,word,M):
    for token in word.split(','):
        r,a=token.split('@');t=rewrite(t,tuple(1 if x=='R' else 0 for x in a),r,M)
    return t

def test_term(t,M):
    w=flat(t,M);nf,trace=normal(t,M);assert nf==canonical(w)
    for a,r in redexes(t):
        q=rewrite(t,a,r,M);assert flat(q,M)==w and normal(q,M)[0]==nf;COUNT['immediate_redexes']+=1
    return w

def run_critical():
    rows=[]
    for name,M in TABLES.items():
        for idx,p in enumerate(SHAPES):
            k,vs=parameters(p);actual=0
            for n in range(3):
                V=tuple(range(n));pairs=tuple(combinations(V,2))
                for eflags in product((0,1),repeat=len(pairs)):
                    E=tuple(e for e,b in zip(pairs,eflags) if b)
                    for assignment in product(range(k),repeat=n):
                        bs=tuple(tuple(i for i,b in enumerate(assignment) if b==j) for j in range(k))
                        for objs in combinations_with_replacement(range(3),k+1):
                            for zs in product((0,1),repeat=k):
                                for values in product(range(len(M)),repeat=len(vs)):
                                    t=instance(p,V,E,bs,objs,zs,dict(zip(sorted(vs),values)));w=test_term(t,M)
                                    a,b=JOINS[idx];assert join(t,a,M)==join(t,b,M)
                                    TRACE.update(repr((name,idx,w)).encode());actual+=1
            expected=sum(2**(n*(n-1)//2)*k**n for n in range(3))*comb(k+3,2)*2**k*len(M)**len(vs)
            assert actual==expected;rows.append(dict(monoid=name,row=idx+1,executed=actual,expected=expected))
    COUNT['T_cases']=sum(r['executed'] for r in rows);assert COUNT['T_cases']==112785
    return rows

def x_instances(p,M):
    k,vs=parameters(p);V=tuple(range(k));graphs=[()]+([((0,k-1),)] if k>=2 else [])
    objs=(1,) if not k else (0,)+(1,)*(k-1)+(2,)
    for E in graphs:
        for zs in ([(0,)*k]+([(1,)+(0,)*(k-1)] if k else [])):
            for vals in product(range(len(M)),repeat=len(vs)):
                yield instance(p,V,E,tuple((i,) for i in V),objs,zs,dict(zip(sorted(vs),vals)))
def contexts(t,M):
    yield t,()
    for v in range(len(M)):yield val(v,t),(0,)
    yield cut(unit(t.arrow[0]),t,t.edges),(1,)
    yield cut(t,unit(t.arrow[1]),t.edges),(0,)
    yield cut(leaf((),(),(t.arrow[0],t.arrow[0],0)),t,t.edges),(1,)
    yield cut(t,leaf((),(),(t.arrow[1],t.arrow[1],0)),t.edges),(0,)
def menu(t,M):
    ls=tuple(l for a,l in occurrences(t));yield ls
    for i,l in enumerate(ls):
        for v in range(len(M)):yield ls[:i]+(val(v,l),)+ls[i+1:]
        for b in product((0,1),repeat=len(l.vertices)):
            V=tuple(x for x,f in zip(l.vertices,b) if f);W=tuple(x for x,f in zip(l.vertices,b) if not f)
            for mid in range(l.arrow[0],l.arrow[1]+1):
                for z in (0,1):
                    q=cut(leaf(V,l.edges,(l.arrow[0],mid,z)),leaf(W,l.edges,(mid,l.arrow[1],z^l.arrow[2])),l.edges)
                    yield ls[:i]+(q,)+ls[i+1:]
        if not l.vertices and l.arrow==(l.arrow[0],l.arrow[0],0):
            for v in range(len(M)):yield ls[:i]+(val(v,unit(l.arrow[0])),)+ls[i+1:]
    for v in range(len(M)):yield tuple(val(v,l) for l in ls)
def eq(t,a,r,M,inverse=False):
    return ('eq',a,r,inverse,t)
def raw(F):return ('raw',F)
def path(source,edges,M):
    current=source;F=tuple(l for a,l in occurrences(source));sem=tuple(flat(f,M) for f in F)
    for edge in edges:
        if edge[0]=='eq':
            _,a,r,inv,target=edge
            assert (rewrite(target,a,r,M)==current if inv else rewrite(current,a,r,M)==target)
            assert tuple(l for a,l in occurrences(current))==tuple(l for a,l in occurrences(target))
            current=target
        else:
            H=edge[1];current=graft(current,H)
            # Assign every newly grafted tree to an (original entry, local address).
            lineage=[(i,a) for i,f in enumerate(F) for a,l in occurrences(f)]
            assert len(lineage)==len(H);new=list(F)
            for (i,a),h in zip(lineage,H):new[i]=alter(new[i],a,h)
            F=tuple(new)
            flatH=tuple(flat(h,M) for h in H);offset=0;newsem=[]
            for e in sem:
                n=len(e[3]);newsem.append(compose(e,flatH[offset:offset+n],M));offset+=n
            assert offset==len(H);sem=tuple(newsem)
    assert compose(flat(source,M),sem,M)==flat(current,M)
    N=tuple(normal(f,M)[0] for f in F);assert tuple(flat(f,M) for f in N)==sem
    return current,N,sem

def square(source,left,right,M,name):
    assert path(source,left,M)==path(source,right,M);COUNT[name]+=1

def min_checks(l,r,rule,M):
    base=leaf(l.vertices,l.edges,l.arrow)
    for host,a in contexts(base,M):
        ls=tuple(q for b,q in occurrences(host));i=[b for b,q in occurrences(host)].index(a)
        F=ls[:i]+(l,)+ls[i+1:];H=ls[:i]+(r,)+ls[i+1:]
        s=graft(host,F);t=graft(host,H);assert rewrite(s,a,rule,M)==t
        square(host,(raw(F),eq(t,a,rule,M)),(raw(H),),M,'MIn')
def run_mixed():
    for name,M in TABLES.items():
        for p in SHAPES:
            for t in x_instances(p,M):test_term(t,M);COUNT['X18_base_terms']+=1
        for rule,p in BARE:
            for l in x_instances(p,M):
                r=rewrite(l,(),rule,M);min_checks(l,r,rule,M)
                for F in menu(l,M):
                    gl=graft(l,F);gr=graft(r,F);assert rewrite(gl,(),rule,M)==gr
                    min_checks(gl,gr,rule,M)
                    for host,a in contexts(l,M):
                        target=alter(host,a,r)
                        # Surrounding external empty leaves must retain their identity entries.
                        start=[q for b,q in occurrences(host)];indices=[i for i,(b,q) in enumerate(occurrences(host)) if b[:len(a)]==a]
                        H=list(start)
                        for i,f in zip(indices,F):H[i]=f
                        H=tuple(H);end=graft(target,H)
                        assert rewrite(graft(host,H),a,rule,M)==end
                        square(host,(eq(target,a,rule,M),raw(H)),(raw(H),eq(end,a,rule,M)),M,'MOut')
                        square(target,(eq(host,a,rule,M,True),raw(H)),(raw(H),eq(graft(host,H),a,rule,M,True)),M,'MOut_inverse')
                sibling=val(0,leaf((),(),(l.arrow[0],l.arrow[0],0)));host=cut(sibling,l,l.edges)
                a=rewrite(host,(0,),'D0',M);ab=rewrite(a,(1,),rule,M)
                b=rewrite(host,(1,),rule,M);ba=rewrite(b,(0,),'D0',M);assert ab==ba
                square(host,(eq(a,(0,),'D0',M),eq(ab,(1,),rule,M)),(eq(b,(1,),rule,M),eq(ba,(0,),'D0',M)),M,'ordinary_disjoint')
                for i,(addr,x) in enumerate(occurrences(l)):
                    F=tuple(val(0,q) if j==i else q for j,(z,q) in enumerate(occurrences(l)));host=graft(l,F)
                    a=rewrite(host,addr,'D0',M);ab=rewrite(a,(),rule,M)
                    b=rewrite(host,(),rule,M);addr2=occurrences(r)[i][0];ba=rewrite(b,addr2,'D0',M);assert ab==ba
                    square(host,(eq(a,addr,'D0',M),eq(ab,(),rule,M)),(eq(b,(),rule,M),eq(ba,addr2,'D0',M)),M,'ordinary_variable')
    
def six():
    V=tuple(range(6));E=((0,5),(1,2),(2,3),(3,4));bs=((0,),(1,2),(3,4),(5,));ars=((0,1,0),(1,1,0),(1,1,0),(1,2,0))
    return canonical((V,E,(0,2,0),bs,ars,0))
def normalized_key(w):
    V,E,a,bs,ars,v=w;pos={x:i for i,x in enumerate(V)}
    return len(V),tuple((pos[x],pos[y]) for x,y in E),a,tuple(tuple(pos[x] for x in b) for b in bs),ars,v

def run_named():
    for name,M in TABLES.items():
        t=six();ls=tuple(l for a,l in occurrences(t));assert normalized_key(flat(ls[1],M))==normalized_key(flat(ls[2],M))
        for src in (t,cut(leaf((),(),(1,1,0)),leaf((),(),(1,1,0)),())):
            for F in menu(src,M):
                mid=graft(src,F);second=[tuple(l for a,l in occurrences(mid))]
                for i,(a,l) in enumerate(occurrences(mid)):
                    base=second[0]
                    second.extend(base[:i]+(val(v,l),)+base[i+1:] for v in range(len(M)))
                    if not l.vertices and l.arrow==(l.arrow[0],l.arrow[0],0):second.append(base[:i]+(unit(l.arrow[0]),)+base[i+1:])
                for H in second:
                    offset=0;K=[]
                    for f in F:
                        k=len(occurrences(f));K.append(graft(f,H[offset:offset+k]));offset+=k
                    assert offset==len(H)
                    square(src,(raw(F),raw(H)),(raw(tuple(K)),),M,'raw_two_stage')
        empty=leaf((),(),(1,1,0))
        for component in ls+(empty,):
            for h in range(9):
                tower=component
                for z in range(h):tower=val(0,tower)
                assert normal(tower,M)[0]==component
                assert sum(q.tag!='l' for q in walk(tower))==h
                COUNT['tower_cases']+=1
        # Nonthin scalar tuples, including noncancellation in E2.
        for srcval in range(len(M)):
            source=flat(val(srcval,t),M);groups=defaultdict(list)
            for values in product(range(len(M)),repeat=4):
                F=tuple(flat(val(v,l),M) for v,l in zip(values,ls));groups[compose(source,F,M)].append(F);COUNT['six_value_tuples']+=1
            if len(M)>1:assert any(len(group)>1 for group in groups.values())
            for group in groups.values():assert len(set(group))==len(group)
        two=cut(empty,empty,());three=cut(empty,two,())
        F=(empty,two);H=(two,empty)
        assert flat(graft(two,F),M)==flat(graft(two,H),M)
        assert tuple(flat(f,M) for f in F)!=tuple(flat(h,M) for h in H)
        assert tuple(sorted(flat(f,M)[5] for f in F))==tuple(sorted(flat(h,M)[5] for h in H));COUNT['segmentation_negative']+=1
        if len(M)>1:
            assert flat(val(1,unit(1)),M)[5]==1;assert flat(val(1,unit(1)),M)!=flat(unit(1),M);COUNT['nullary_negative']+=1
        bad=leaf((),(),(1,1,1));assert flat(bad,M)!=flat(unit(1),M);COUNT['grade_negative']+=1
        weakened=replace(t,edges=((1,2),(2,3),(3,4)));assert flat(weakened,M)!=flat(t,M)
        assert tuple(l.edges for a,l in occurrences(weakened))==tuple(l.edges for a,l in occurrences(t));COUNT['whole_negative']+=1
        def split(l):
            return cut(leaf(l.vertices[:1],l.edges,l.arrow),leaf(l.vertices[1:],l.edges,l.arrow),l.edges)
        F=ls[:1]+(split(ls[1]),)+ls[2:];H=ls[:2]+(split(ls[2]),)+ls[3:]
        assert flat(graft(t,F),M)!=flat(graft(t,H),M);COUNT['occurrence_negative']+=1
        # Well-typed corrupt residual at the wrong of two equal components.
        dF=ls[:1]+(val(0,ls[1]),)+ls[2:];dH=ls[:2]+(val(0,ls[2]),)+ls[3:]
        assert graft(t,dF)!=graft(t,dH) and flat(graft(t,dF),M)==flat(graft(t,dH),M)
        correct=occurrences(t)[1][0];wrong=occurrences(t)[2][0]
        caught=False
        try:rewrite(graft(t,dF),wrong,'D0',M)
        except AssertionError:caught=True
        assert caught;assert rewrite(graft(t,dF),correct,'D0',M)==t;COUNT['wrong_residual_negative']+=1

def walk(t):
    yield t
    for c in t.children:yield from walk(c)
def main():
    start=time.monotonic();rows=run_critical();print('Independent T passed',COUNT['T_cases'],flush=True)
    run_mixed();print('Independent mixed subset passed',flush=True)
    run_named();print('Independent named and raw paths passed',flush=True)
    report={'status':'PASS','reviewer':'/root/audit_completion_finite_certificates','representation':'independent global vertex incidence, no author imports','domain_sha256':hashlib.sha256((P/'REVIEW_DOMAIN.md').read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'counts':dict(COUNT),'T_rows':rows,'trace_sha256':TRACE.hexdigest(),'elapsed_seconds':time.monotonic()-start,'not_claimed':['full author X/H/F replay','unrestricted ordinary/mixed coherence','scientific acceptance','novelty']}
    (P/'IndependentNoImportCertificate.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
