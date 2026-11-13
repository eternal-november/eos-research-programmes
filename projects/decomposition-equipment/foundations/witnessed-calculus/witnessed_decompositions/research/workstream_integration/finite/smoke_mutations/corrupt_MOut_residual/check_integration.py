#!/usr/bin/env python3
"""Bounded author C evidence for reviewed DOMAIN.md; no unrestricted theorem."""
from model import *
from collections import Counter,defaultdict
from math import comb
from pathlib import Path
import hashlib,json,time,traceback

HERE=Path(__file__).resolve().parent
COUNTS=Counter();TRACE=hashlib.sha256()
JOIN_WORDS=[
 ('R@,UR@R','UR@'),('R@,DR@R,DR@','DR@,R@D'),('UL@','UR@'),
 ('UL@','DR@,UL@D'),('UR@','DL@,UR@D'),('DL@,DR@D,DA@','DR@,DL@D,DA@'),
 ('D0@','DA@'),('R@,R@','R@L,R@,R@R'),('R@,UL@','UL@L'),('R@,UL@R','UR@L'),
 ('R@,DL@','DL@L,DL@,R@D'),('R@,DL@R,DR@','DR@L,DL@,R@D'),
 ('DA@,DA@','DA@D,DA@'),('DA@','D0@D'),('DL@,DL@D,DA@','DA@L,DL@'),
 ('DL@,D0@','D0@L'),('DR@,DR@D,DA@','DA@R,DR@'),('DR@,D0@','D0@R')]

def record(name,item=None):
    COUNTS[name]+=1
    if item is not None:TRACE.update((name+repr(item)+'\n').encode())

def pc(x,y):return ('C',x,y)
def pd(m,x):return ('D',m,x)
PATTERNS=[pc(pc('x','y'),'u'),pc(pc('x','y'),pd('m','z')),pc('u','u'),pc('u',pd('m','x')),pc(pd('m','x'),'u'),pc(pd('m','x'),pd('n','y')),pd(0,pd('n','x')),pc(pc(pc('x','y'),'z'),'w'),pc(pc('u','x'),'y'),pc(pc('x','u'),'y'),pc(pc(pd('m','x'),'y'),'z'),pc(pc('x',pd('m','y')),'z'),pd('m',pd('n',pd('p','x'))),pd('m',pd(0,'x')),pc(pd('m',pd('n','x')),'y'),pc(pd(0,'x'),'y'),pc('x',pd('m',pd('n','y'))),pc('x',pd(0,'y'))]
BARE=[('R',pc(pc('x','y'),'z')),('UL',pc('u','x')),('UR',pc('x','u')),('D0',pd(0,'x')),('DA',pd('m',pd('n','x'))),('DL',pc(pd('m','x'),'y')),('DR',pc('x',pd('m','y')))]

def symbols(p):
    if isinstance(p,str):return ([] if p=='u' else [p],set())
    if p[0]=='D':
        ls,vs=symbols(p[2]);return ls,vs|({p[1]} if isinstance(p[1],str) else set())
    a,b=symbols(p[1]);c,d=symbols(p[2]);return a+c,b|d

def realize(pattern,g,blocks,arrows,objects,values):
    cursor=0
    def go(p):
        nonlocal cursor
        if p=='u':return U(objects[cursor]),()
        if isinstance(p,str):
            vs=blocks[cursor];t=L(g.restrict(vs),arrows[cursor]);cursor+=1;return t,vs
        if p[0]=='D':
            q,vs=go(p[2]);return D(values[p[1]] if isinstance(p[1],str) else p[1],q),vs
        x,vx=go(p[1]);y,vy=go(p[2]);vs=tuple(sorted(vx+vy))
        return C(g.restrict(vs),tuple(vs.index(v) for v in vx),x,y),vs
    t,vs=go(pattern);assert cursor==len(blocks) and vs==tuple(range(g.n));return t

def contexts(t,M):
    yield 'id',t,()
    for v in range(M.size):yield 'D'+str(v),D(v,t),(0,)
    yield 'UL',C(t.graph,(),U(t.arrow.a),t),(1,)
    yield 'UR',C(t.graph,tuple(range(t.graph.n)),t,U(t.arrow.b)),(0,)
    yield 'EL',C(t.graph,(),L(Graph(0),Arrow(t.arrow.a,t.arrow.a)),t),(1,)
    yield 'ER',C(t.graph,tuple(range(t.graph.n)),t,L(Graph(0),Arrow(t.arrow.b,t.arrow.b))),(0,)

def forest_menu(t,M):
    ls=tuple(leaves(t));yield ls
    for i,l in enumerate(ls):
        for v in range(M.size):yield ls[:i]+(D(v,l),)+ls[i+1:]
        for bits in product((0,1),repeat=l.graph.n):
            left=tuple(j for j,b in enumerate(bits) if b);right=tuple(j for j,b in enumerate(bits) if not b)
            for mid in range(l.arrow.a,l.arrow.b+1):
                for z in (0,1):
                    x=L(l.graph.restrict(left),Arrow(l.arrow.a,mid,z));y=L(l.graph.restrict(right),Arrow(mid,l.arrow.b,z^l.arrow.z))
                    q=C(l.graph,left,x,y);yield ls[:i]+(q,)+ls[i+1:]
        if l.graph.n==0 and l.arrow==Arrow(l.arrow.a,l.arrow.a):
            for v in range(M.size):yield ls[:i]+(D(v,U(l.arrow.a)),)+ls[i+1:]
    for v in range(M.size):yield tuple(D(v,l) for l in ls)

def residual(t,F,addr,rule,M):
    # MUTATION_POINT MOut: do not permute the common forest.
    ls=leaves(t)
    bad=list(F)
    for i in range(len(ls)):
        for j in range(i+1,len(ls)):
            if (ls[i].graph,ls[i].arrow)==(ls[j].graph,ls[j].arrow) and F[i]!=F[j]:
                bad[i],bad[j]=bad[j],bad[i]
                return apply_step(graft(t,tuple(bad)),addr,rule,M)
    return apply_step(graft(t,F),addr,rule,M)

def eq_trace(source,M):
    cur=source;out=[]
    for addr,rule in normalize(source,M)[1]:
        q=apply_step(cur,addr,rule,M);out.append(Eq(q,addr,rule));cur=q
    return tuple(out)

def check_paths(source,left,right,M,kind):
    if kind.startswith('MIn'):assert 'MIn' in MIXED_SCHEMAS,'MIn certificate not admitted by syntactic basis'
    if kind.startswith('MOut'):assert 'MOut' in MIXED_SCHEMAS,'MOut certificate not admitted by syntactic basis'
    f,u=path_normalize(source,left,M);g,v=path_normalize(source,right,M)
    assert u==v,(kind,'different endpoints')
    assert f==g,(kind,'different syntactically normalized forests')
    sf,su=semantic_path(source,left,M);sg,sv=semantic_path(source,right,M)
    assert sf==sg and su==sv==u
    assert tuple(address_evaluation(t,M) for t in f)==sf
    record('paths_'+kind,(len(left),len(right),len(f),tuple(node_count(q) for q in f)))

def explicit_join(t,row,M):
    def path(word):
        q=t;out=[]
        for token in word.split(','):
            rule,address=token.split('@');addr=tuple(1 if c=='R' else 0 for c in address)
            q=apply_step(q,addr,rule,M);out.append(Eq(q,addr,rule))
        return tuple(out)
    a,b=JOIN_WORDS[row-1];check_paths(t,path(a),path(b),M,'declared_O_'+str(row))

def check_term(t,M):
    w=evaluation(t,M);assert w==address_evaluation(t,M) and w.valid()
    nf,tr=normalize(t,M);assert nf==canonical(w,M) and not steps(nf,M)
    for addr,rule,q in steps(t,M):
        assert evaluation(q,M)==w and address_evaluation(q,M)==w
        assert measure(q)<measure(t)
        assert normalize(q,M)[0]==nf
        record('one_step_reducts')
    record('tree_checks',(M.name,t.arrow,w.blocks,w.value,len(tr)))

def x_realizations(pattern,M):
    ls,vs=symbols(pattern);k=len(ls)
    gs=[Graph(k)]
    if k>=2:gs.append(Graph(k,((0,k-1),)))
    objs=(1,) if k==0 else ((0,2) if k==1 else (0,)+(1,)*(k-1)+(2,))
    grades=[(0,)*k]
    if k:grades.append((1,)+(0,)*(k-1))
    for g in gs:
        for zs in grades:
            ars=tuple(Arrow(objs[i],objs[i+1],zs[i]) for i in range(k))
            for vals in product(range(M.size),repeat=len(vs)):
                yield realize(pattern,g,tuple((i,) for i in range(k)),ars,objs,dict(zip(sorted(vs),vals)))

def check_mout(t,u,addr,rule,F,M):
    q=residual(t,F,addr,rule,M);assert q==graft(u,F),'well-typed MOut residual target disagrees with positional graft'
    check_paths(t,(Eq(u,addr,rule),Raw(F)),(Raw(F),Eq(q,addr,rule)),M,'MOut')
    check_paths(u,(Eq(t,addr,rule,True),Raw(F)),(Raw(F),Eq(graft(t,F),addr,rule,True)),M,'MOut_inverse')

def leaf_addresses(t):
    if t.kind=='L':return ((),)
    return tuple((i,)+a for i,c in enumerate(t.children) for a in leaf_addresses(c))

def check_min_pair(l,r,rule,M):
    for name,host,prefix in contexts(L(l.graph,l.arrow),M):
        idx=leaf_addresses(host).index(prefix)
        base=tuple(leaves(host));Fl=base[:idx]+(l,)+base[idx+1:];Fr=base[:idx]+(r,)+base[idx+1:]
        a=graft(host,Fl);b=graft(host,Fr);assert apply_step(a,prefix,rule,M)==b
        check_paths(host,(Raw(Fl),Eq(b,prefix,rule)),(Raw(Fr),),M,'MIn')
        record('min_context_'+name)


def named_controls():
    ars=tuple(Arrow(a,b,z) for a in range(3) for b in range(a,3) for z in (0,1))
    for f in ars:
        assert Arrow(f.a,f.a).then(f)==f==f.then(Arrow(f.b,f.b))
        for g in ars:
            if f.b!=g.a:continue
            for h in ars:
                if g.b==h.a:assert f.then(g).then(h)==f.then(g.then(h));record('category_associativity')
    for g in graphs(2):assert g.n<=2<=6;record('literal_bound_inclusions')
    for M in MONOIDS:
        for a in range(M.size):
            assert M.mul(0,a)==M.mul(a,0)==a
            for b in range(M.size):
                assert M.mul(a,b)==M.mul(b,a)
                for c in range(M.size):assert M.mul(M.mul(a,b),c)==M.mul(a,M.mul(b,c))
        x=L(Graph(1),Arrow(0,1));l=D(0,x)
        check_paths(x,(Raw((l,)),Eq(x,(),'D0')),(Raw((x,)),),M,'MIn_d0_control')
        if M.size>1:
            q=D(1,U(1));assert evaluation(q,M)==address_evaluation(q,M),'decorated nullary value disagrees with root-address evaluator'
            assert evaluation(q,M).value==1
            t=C(Graph(1),(),q,L(Graph(1),Arrow(1,2)));check_term(t,M)
        empty=L(Graph(0),Arrow(1,1));two=C(Graph(0),(),empty,empty)
        three=C(Graph(0),(),empty,two)
        F=(empty,two);H=(two,empty)
        assert evaluation(graft(two,F),M)==evaluation(graft(two,H),M)
        assert arrow_key(tuple(evaluation(x,M) for x in F))!=arrow_key(tuple(evaluation(x,M) for x in H)), 'entry profile collision'
        bad=L(Graph(0),Arrow(1,1,1));assert bad!=U(1) and len(evaluation(bad,M).blocks)==1
        # Actual graph equality does not identify output grades.
        a=flat_identity(Graph(0),Arrow(1,1));b=flat_identity(Graph(0),Arrow(1,1,1))
        assert hom_decode(a,b,M)==set()
        # Two different leaves with equal profiles do not make identical cuts.
        a=Flat(Graph(2),Arrow(0,2),((0,),(1,)),(Arrow(0,1),Arrow(1,2)),0)
        b=replace(a,blocks=((1,),(0,)))
        assert a.profile==b.profile and a!=b and canonical(a,M)!=canonical(b,M)
        # Missing-DL and reverse-rotation controls are explicit finite syntax.
        t=realize(PATTERNS[11],Graph(3,((0,2),)),((0,),(1,),(2,)),(Arrow(0,1),Arrow(1,1),Arrow(1,2)),(0,1,1,2),{'m':min(1,M.size-1)})
        if M.size>1:
            def norm_omit_dl(s):
                while True:
                    opts=[x for x in steps(s,M) if x[1]!='DL']
                    if not opts:return s
                    s=opts[0][2]
            ends={norm_omit_dl(q) for address,rule,q in steps(t,M) if rule!='DL'}
            assert len(ends)>=2
        r=next(q for addr,rule,q in steps(t,M) if addr==() and rule=='R')
        assert r!=t and measure(r)<measure(t)
        ordinary_localization_control(M)
        record('named_negative_control')
        named_six(M)

def ordinary_localization_control(M):
    t=next(x_realizations(PATTERNS[7],M))
    def edges(word):
        cur=t;out=[]
        for token in word.split(','):
            rule,address=token.split('@');addr=tuple(1 if c=='R' else 0 for c in address)
            q=apply_step(cur,addr,rule,M);out.append(((cur,addr,rule,q),1));cur=q
        return cur,out
    end,a=edges(JOIN_WORDS[7][0]);other,b=edges(JOIN_WORDS[7][1]);assert end==other
    loop=a+[(edge,-sign) for edge,sign in reversed(b)];reduced=[]
    for edge,sign in loop:
        if reduced and reduced[-1]==(edge,-sign):reduced.pop()
        else:reduced.append((edge,sign))
    assert len(reduced)==5,'the missing-O free groupoid pentagon loop should not freely cancel'
    record('ordinary_localization_nontrivial_loops',len(reduced))
    if M.size>1:
        x=flat_identity(Graph(1),Arrow(1,1));y=replace(x,value=1)
        assert x!=y and map_flat(x,lambda x:x,(0,)*M.size)==map_flat(y,lambda x:x,(0,)*M.size)
        record('witness_collapse_controls')


def six_term(M):
    g=Graph(6,((0,5),(1,2),(2,3),(3,4)));bs=((0,),(1,2),(3,4),(5,))
    fs=(Arrow(0,1),Arrow(1,1),Arrow(1,1),Arrow(1,2))
    return canonical(Flat(g,Arrow(0,2),bs,fs,0),M)

def named_six(M):
    t=six_term(M);ls=leaves(t)
    for slot,x in enumerate(ls+(L(Graph(0),Arrow(1,1)),)):
        for h in range(9):
            tower=x
            for _ in range(h):tower=D(0,tower)
            assert node_count(tower)==h and normalize(tower,M)[0]==x
            check_paths(x,(Raw((tower,)),)+eq_trace(tower,M),(Raw((x,)),),M,'MIn_tower')
            record('tower_heights',(slot,x.graph,x.arrow,h))
    assert (ls[1].graph,ls[1].arrow)==(ls[2].graph,ls[2].arrow)
    split=C(ls[1].graph,(0,),L(Graph(1),Arrow(1,1)),L(Graph(1),Arrow(1,1)))
    F=ls[:1]+(split,)+ls[2:];H=ls[:2]+(split,)+ls[3:]
    a=dispatch_graft(t,F);b=dispatch_graft(t,H)
    assert evaluation(a,M)==flat_compose(address_evaluation(t,M),tuple(address_evaluation(q,M) for q in F),M),'positional raw graft disagrees with independent flat substitution'
    assert evaluation(b,M)==flat_compose(address_evaluation(t,M),tuple(address_evaluation(q,M) for q in H),M),'positional raw graft disagrees with independent flat substitution'
    assert evaluation(a,M)!=evaluation(b,M),'equal repeated occurrences merged'
    for srcval in range(M.size):
        src=replace(evaluation(t,M),value=srcval);groups=defaultdict(list)
        for vals in product(range(M.size),repeat=4):
            es=tuple(replace(flat_identity(l.graph,l.arrow),value=v) for l,v in zip(ls,vals))
            tgt=flat_compose(src,es,M);groups[tgt].append(es)
            assert es in hom_decode(src,tgt,M);record('six_label_tuples')
            # Cross-product of ALL source/local values with each positional proper split.
            labelled_source=t if srcval==0 else D(srcval,t)
            splitF=ls[:1]+(split,)+ls[2:];splitH=ls[:2]+(split,)+ls[3:]
            splitF=tuple(q if v==0 else D(v,q) for q,v in zip(splitF,vals))
            splitH=tuple(q if v==0 else D(v,q) for q,v in zip(splitH,vals))
            actualF=dispatch_graft(labelled_source,splitF);actualH=dispatch_graft(labelled_source,splitH)
            expectedF=flat_compose(src,tuple(address_evaluation(q,M) for q in splitF),M)
            expectedH=flat_compose(src,tuple(address_evaluation(q,M) for q in splitH),M)
            assert evaluation(actualF,M)==expectedF and evaluation(actualH,M)==expectedH,'labelled positional raw graft disagrees with independent flat substitution'
            assert expectedF!=expectedH
            record('six_positional_split_value_assignments')
        if M.size>1:
            assert any(len(v)>1 for v in groups.values())
            for group in groups.values():assert len({arrow_key(x) for x in group})==len(group)
    g0=Graph(6,((1,2),(2,3),(3,4)))
    assert tuple(t.graph.restrict(B) for B in evaluation(t,M).blocks)==tuple(g0.restrict(B) for B in evaluation(t,M).blocks)
    assert replace(evaluation(t,M),graph=g0)!=evaluation(t,M)
    # MOut mutation is detected on distinct typed/repeated occurrences.
    e=D(0,t);check_mout(e,t,(),'D0',F,M)
    check_transport(t,M)
    record('six_main')


def run_T():
    per=[]
    for M in MONOIDS:
        for row,patt in enumerate(PATTERNS,1):
            ls,vs=symbols(patt);k=len(ls);d=len(vs);count=0
            for g in graphs(2):
                for bs in partitions(g.n,k):
                    for obj,ars in strings(k,True):
                        for vals in product(range(M.size),repeat=d):
                            t=realize(patt,g,bs,ars,obj,dict(zip(sorted(vs),vals)))
                            check_term(t,M);explicit_join(t,row,M);count+=1
            expected=sum((2**(r*(r-1)//2))*(k**r)*comb(k+3,2)*(2**k)*(M.size**d) for r in range(3))
            assert count==expected
            per.append({'monoid':M.name,'row':row,'executed':count,'formula':expected})
            evaluation.cache_clear()
    return per


def abstract_redex(t,rule,M):
    """Recover the bare labelled template AND its exact ordered metavariable forest."""
    def ident(x):return L(x.graph,x.arrow)
    if rule=='R':
        xy,z=t.children;x,y=xy.children;F=(x,y,z)
        bare=replace(t,children=(replace(xy,children=(ident(x),ident(y))),ident(z)))
    elif rule=='UL':
        unit,x=t.children;F=(x,);bare=replace(t,children=(unit,ident(x)))
    elif rule=='UR':
        x,unit=t.children;F=(x,);bare=replace(t,children=(ident(x),unit))
    elif rule=='D0':
        x=t.children[0];F=(x,);bare=replace(t,children=(ident(x),))
    elif rule=='DA':
        d=t.children[0];x=d.children[0];F=(x,)
        bare=replace(t,children=(replace(d,children=(ident(x),)),))
    elif rule=='DL':
        d,y=t.children;x=d.children[0];F=(x,y)
        bare=replace(t,children=(replace(d,children=(ident(x),)),ident(y)))
    elif rule=='DR':
        x,d=t.children;y=d.children[0];F=(x,y)
        bare=replace(t,children=(ident(x),replace(d,children=(ident(y),))))
    else:raise AssertionError(('unknown rule',rule))
    right=apply_step(bare,(),rule,M)
    assert graft(bare,F)==t
    assert graft(right,F)==apply_step(t,(),rule,M)
    assert tuple((x.graph,x.arrow) for x in leaves(bare))==tuple((x.graph,x.arrow) for x in F)
    record('MIn_extraction_restore_checks',(rule,t.graph,t.arrow))
    return bare,F

def check_bare_case(rule,l,M,scope,smoke=False):
    r=apply_step(l,(),rule,M);check_min_pair(l,r,rule,M)
    menu=tuple(forest_menu(l,M))
    if smoke:menu=menu[:2]+menu[-2:]
    for F in menu:
        q=graft(l,F);v=graft(r,F)
        assert apply_step(q,(),rule,M)==v
        check_min_pair(q,v,rule,M)
    # Explicit disjoint square in a fresh sibling.
    e=D(0,L(Graph(0),Arrow(l.arrow.a,l.arrow.a)));host=C(l.graph,(),e,l)
    a=apply_step(host,(0,),'D0',M);ab=apply_step(a,(1,),rule,M)
    b=apply_step(host,(1,),rule,M);ba=apply_step(b,(0,),'D0',M)
    assert ab==ba
    check_paths(host,(Eq(a,(0,),'D0'),Eq(ab,(1,),rule)),(Eq(b,(1,),rule),Eq(ba,(0,),'D0')),M,'ordinary_disjoint')
    for i,x in enumerate(leaves(l)):
        F=list(leaves(l));F[i]=D(0,x);F=tuple(F);host=graft(l,F)
        a=apply_step(host,leaf_addresses(l)[i],'D0',M);ab=apply_step(a,(),rule,M)
        b=apply_step(host,(),rule,M);ba=apply_step(b,leaf_addresses(r)[i],'D0',M)
        assert ab==ba
        check_paths(host,(Eq(a,leaf_addresses(l)[i],'D0'),Eq(ab,(),rule)),(Eq(b,(),rule),Eq(ba,leaf_addresses(r)[i],'D0')),M,'ordinary_variable')
    record('MIn_checked_'+scope,(rule,l.graph,l.arrow,len(leaves(l))))


def run_X():
    for M in MONOIDS:
        extracted=set();base_cases=set()
        for row,patt in enumerate(PATTERNS,1):
            for base in x_realizations(patt,M):
                for addr,rule,u in steps(base,M):
                    bare,inst=abstract_redex(at(base,addr),rule,M)
                    extracted.add((rule,bare));record('MIn_X_redex_occurrences')
                check_transport(base,M)
                for cname,t,prefix in contexts(base,M):
                    for addr,rule,u in steps(base,M):
                        # Replace exactly the original hole of the chosen surrounding context.
                        target=replace_at(t,prefix,u);a=prefix+addr
                        assert apply_step(t,a,rule,M)==target
                        for F in forest_menu(t,M):check_mout(t,target,a,rule,F,M)
                    record('X_context_'+cname)
                evaluation.cache_clear()
                for addr,rule,u in steps(base,M):
                    path=(Eq(u,addr,rule),)+eq_trace(u,M)
                    direct=eq_trace(base,M)
                    check_paths(base,path,direct,M,'ordinary_peak_join')
        for rule,patt in BARE:
            for l in x_realizations(patt,M):
                base_cases.add((rule,l));check_bare_case(rule,l,M,'base')
        extras=extracted-base_cases
        for rule,l in sorted(extras,key=repr):check_bare_case(rule,l,M,'expanded')
        COUNTS['MIn_X_extracted_unique']+=len(extracted)
        COUNTS['MIn_base_unique']+=len(base_cases)
        COUNTS['MIn_expanded_unique']+=len(extras)
        COUNTS['MIn_union_unique']+=len(base_cases|extracted)
        assert len(base_cases|extracted)==len(base_cases)+len(extras)
        print('X monoid',M.name,'base bare',len(base_cases),'extracted',len(extracted),'additional',len(extras),flush=True)
        for source in (six_term(M),C(Graph(0),(),L(Graph(0),Arrow(1,1)),L(Graph(0),Arrow(1,1)))):
            for F in forest_menu(source,M):
                mid=graft(source,F);ls=leaves(mid);second=[tuple(ls)]
                for i,l in enumerate(ls):
                    for v in range(M.size):second.append(ls[:i]+(D(v,l),)+ls[i+1:])
                    if l.graph.n==0 and l.arrow==Arrow(l.arrow.a,l.arrow.a):second.append(ls[:i]+(U(l.arrow.a),)+ls[i+1:])
                for H in second:
                    K=compose_forest(F,H)
                    check_paths(source,(Raw(F),Raw(H)),(Raw(K),),M,'raw_composition')
                    srcflat=address_evaluation(source,M);ff=tuple(address_evaluation(q,M) for q in F);hh=tuple(address_evaluation(q,M) for q in H)
                    check_raw_flat_pair(srcflat,ff,hh,address_evaluation(graft(source,K),M),M,'named_raw_flat_pairs')
                    target=graft(mid,H);check_paths(source,(Raw(F),Raw(H))+eq_trace(target,M),(Raw(K),)+eq_trace(target,M),M,'raw_then_equations')
        evaluation.cache_clear()


def check_raw_flat_pair(src,F,H,tgt,M,label):
    # Reify EACH semantic entry independently, then use actual raw forest grafting.
    root=canonical(src,M);rawF=tuple(canonical(e,M) for e in F);rawH=tuple(canonical(e,M) for e in H)
    rawK=compose_forest(rawF,rawH)
    final_sequential=graft(graft(root,rawF),rawH)
    final_composed=graft(root,rawK)
    assert final_sequential==final_composed
    semanticK=tuple_compose(F,H,M)
    assert tuple(address_evaluation(q,M) for q in rawK)==semanticK
    assert address_evaluation(final_composed,M)==tgt==flat_compose(src,semanticK,M)
    assert evaluation(final_sequential,M)==tgt
    record(label,(len(F),len(H),len(tgt.blocks)))


def run_H():
    for M in MONOIDS:
        for g in graphs(2):
            for a in range(3):
                for b in range(a,3):
                    whole=Arrow(a,b)
                    objs=tuple(w for k in range(4) for w in catalog(g,whole,k,M))
                    for src in objs:
                        encoded=defaultdict(set)
                        for es,tgt in tuple_encoder(src,3,M):
                            encoded[tgt].add(arrow_key(es));record('H_encoder_arrows')
                        for tgt in objs:
                            dec=hom_decode(src,tgt,M);assert dec==encoded.get(tgt,set())
                            record('H_hom_pairs');COUNTS['H_arrow_count']+=len(dec)
                            if len(dec)>1:record('H_nonthin_homs')
                            if not dec:record('H_empty_homs')
                        record('H_sources')
    for M in MONOIDS:
        for g in graphs(1):
            for a in range(3):
                for b in range(a,3):
                    for k in range(3):
                        for src in catalog(g,Arrow(a,b),k,M):
                            identity=tuple(flat_identity(*p) for p in src.profile)
                            for F,mid in tuple_encoder(src,2,M):
                                midid=tuple(flat_identity(*p) for p in mid.profile)
                                assert tuple_compose(identity,F,M)==F
                                assert tuple_compose(F,midid,M)==F
                                for H,tgt in tuple_encoder(mid,2,M):
                                    K=tuple_compose(F,H,M)
                                    assert flat_compose(src,K,M)==tgt and K in hom_decode(src,tgt,M)
                                    check_raw_flat_pair(src,F,H,tgt,M,'Hcomp_raw_pairs')
                                    record('Hcomp_pairs')


def map_arrow(a,om,zmap=lambda z:z):return Arrow(om(a.a),om(a.b),zmap(a.z))
@lru_cache(maxsize=100000)
def term_objects(t):
    return tuple(sorted({t.arrow.a,t.arrow.b}.union(*(set(term_objects(c)) for c in t.children))))
@lru_cache(maxsize=200000)
def _map_term(t,object_map,hm,ztable):
    om=dict(object_map)
    return replace(t,arrow=Arrow(om[t.arrow.a],om[t.arrow.b],ztable[t.arrow.z]),value=hm[t.value] if t.kind=='D' else t.value,children=tuple(_map_term(c,object_map,hm,ztable) for c in t.children))
def map_term(t,om,hm,zmap=lambda z:z):
    return _map_term(t,tuple((a,om(a)) for a in term_objects(t)),tuple(hm),(zmap(0),zmap(1)))
def map_flat(w,om,hm,zmap=lambda z:z):return replace(w,whole=map_arrow(w.whole,om,zmap),arrows=tuple(map_arrow(a,om,zmap) for a in w.arrows),value=hm[w.value])
@lru_cache(None)
def homs(M,N):
    return tuple(h for h in product(range(N.size),repeat=M.size) if h[0]==0 and all(h[M.mul(a,b)]==N.mul(h[a],h[b]) for a in range(M.size) for b in range(M.size)))

def check_transport(t,M):
    w=address_evaluation(t,M)
    rawcases=tuple((F,tuple(address_evaluation(q,M) for q in F),graft(t,F)) for F in forest_menu(t,M))
    rawcases=tuple((F,ef,gt,flat_compose(w,ef,M)) for F,ef,gt in rawcases)
    oms=tuple(combinations_with_replacement(range(3),3))
    for N in MONOIDS:
        for hm in homs(M,N):
            for om in oms:
                for collapse in (False,True):
                    zm=(lambda z:0) if collapse else (lambda z:z)
                    mapped=map_term(t,lambda x:om[x],hm,zm)
                    assert address_evaluation(mapped,N)==map_flat(w,lambda x:om[x],hm,zm)
                    assert normalize(map_term(normalize(t,M)[0],lambda x:om[x],hm,zm),N)[0]==normalize(mapped,N)[0]
                    for addr,rule,u in steps(t,M):
                        mu=map_term(u,lambda x:om[x],hm,zm)
                        assert apply_step(mapped,addr,rule,N)==mu
                    for F,ef,gt,et in rawcases:
                        mF=tuple(map_term(q,lambda x:om[x],hm,zm) for q in F)
                        assert map_term(gt,lambda x:om[x],hm,zm)==graft(mapped,mF)
                        mf=tuple(map_flat(e,lambda x:om[x],hm,zm) for e in ef)
                        assert all(me.profile==tuple((g,map_arrow(a,lambda x:om[x],zm)) for g,a in e.profile) for e,me in zip(ef,mf))
                        assert flat_compose(address_evaluation(mapped,N),mf,N)==map_flat(et,lambda x:om[x],hm,zm)
                        record('transport_raw_edges')
                    record('transport_maps')
    graph_coordinates(w)
    ids=tuple(range(M.size));labels=(4,7,9)
    rel=map_term(t,lambda x:labels[x],ids)
    back=map_term(rel,lambda x:labels.index(x),ids)
    assert back==t
    assert map_term(back,lambda x:labels[x],ids)==rel
    record('interface_rename_inverse_pairs')
    # Every composable pair of the 10 object endomaps, at the whole term.
    for f in oms:
        for g in oms:
            for zf in (0,1):
                for zg in (0,1):
                    assert map_term(map_term(t,lambda x:f[x],ids,lambda z:zf*z),lambda x:g[x],ids,lambda z:zg*z)==map_term(t,lambda x:g[f[x]],ids,lambda z:zg*zf*z)
                    record('object_transport_composites')
    for N in MONOIDS:
        for h in homs(M,N):
            for P in MONOIDS:
                for k in homs(N,P):
                    assert map_term(map_term(t,lambda x:x,h),lambda x:x,k)==map_term(t,lambda x:x,tuple(k[h[x]] for x in range(M.size)))
                    record('monoid_transport_composites')


def graph_coordinates(w):
    r=w.graph.n
    assert r in (0,1,2,3,4,6)
    carriers=(tuple(range(r)),tuple(10+2*i for i in range(r)),tuple(100+3*i for i in range(r)))
    for carrier in carriers:
        edges=tuple((carrier[i],carrier[j]) for i,j in w.graph.edges)
        blocks=tuple(tuple(carrier[i] for i in B) for B in w.blocks)
        rank={v:i for i,v in enumerate(carrier)}
        assert tuple((rank[a],rank[b]) for a,b in edges)==w.graph.edges
        assert tuple(tuple(rank[v] for v in B) for B in blocks)==w.blocks
        for B,LB in zip(w.blocks,blocks):
            for bits in product((0,1),repeat=len(B)):
                V=tuple(B[i] for i,b in enumerate(bits) if b)
                LV=tuple(LB[i] for i,b in enumerate(bits) if b)
                induced=tuple((i,j) for i in range(len(LV)) for j in range(i+1,len(LV)) if (LV[i],LV[j]) in edges)
                assert Graph(len(V),induced)==w.graph.restrict(V)
                ranks=tuple(i for i,b in enumerate(bits) if b)
                assert w.graph.restrict(B).restrict(ranks)==w.graph.restrict(V)
                record('graph_nested_restrictions')
                record('graph_coordinate_restrictions')
        record('graph_coordinate_maps')
    # Composition psi(phi(i)) equals the direct third carrier, with literal inverses.
    phi=dict(zip(carriers[0],carriers[1]));psi=dict(zip(carriers[1],carriers[2]))
    first_edges=tuple((phi[a],phi[b]) for a,b in w.graph.edges)
    first_blocks=tuple(tuple(phi[v] for v in B) for B in w.blocks)
    assert tuple((psi[a],psi[b]) for a,b in first_edges)==tuple((carriers[2][a],carriers[2][b]) for a,b in w.graph.edges)
    assert tuple(tuple(psi[v] for v in B) for B in first_blocks)==tuple(tuple(carriers[2][v] for v in B) for B in w.blocks)
    record('graph_edge_block_composites')
    iphi={v:k for k,v in phi.items()};ipsi={v:k for k,v in psi.items()}
    composite={i:psi[phi[i]] for i in range(r)};icomposite={v:i for i,v in composite.items()}
    assert tuple(composite[i] for i in range(r))==carriers[2]
    for forward,back,source,target in ((phi,iphi,carriers[0],carriers[1]),(psi,ipsi,carriers[1],carriers[2]),(composite,icomposite,carriers[0],carriers[2])):
        assert tuple(back[forward[v]] for v in source)==source
        assert tuple(forward[back[v]] for v in target)==target
        record('graph_coordinate_inverse_pairs')


def forced_factor(w,i,j,a,b):
    union=tuple(sorted(v for U0 in w.blocks[i:j] for v in U0));positions={v:k for k,v in enumerate(union)}
    middle=compose(w.arrows[i:j],w.arrows[i].a)
    inner=Flat(w.graph.restrict(union),middle,tuple(tuple(positions[v] for v in U0) for U0 in w.blocks[i:j]),w.arrows[i:j],b)
    outer=Flat(w.graph,w.whole,w.blocks[:i]+(union,)+w.blocks[j:],w.arrows[:i]+(middle,)+w.arrows[j:],a)
    return outer,inner

@lru_cache(None)
def factor_structures(w,i,j):
    # Independent brute force: candidate intermediate graphs and all inner/outer partitions.
    assert w.value==0
    source_profile=w.profile;interval=source_profile[i:j];mid=compose(w.arrows[i:j],w.arrows[i].a)
    op=source_profile[:i]+((None,mid),)+source_profile[j:]
    out=[]
    for K in graphs(w.graph.n):
        expected=op[:i]+((K,mid),)+op[i+1:]
        for ob in partitions(w.graph.n,len(expected)):
            outer=Flat(w.graph,w.whole,ob,w.arrows[:i]+(mid,)+w.arrows[j:],0)
            if outer.profile!=expected:continue
            for ib in partitions(K.n,j-i):
                inner=Flat(K,mid,ib,w.arrows[i:j],0)
                if inner.profile==interval:out.append((outer,inner))
    return tuple(out)

def check_factor(w,i,j,M):
    expected={forced_factor(w,i,j,a,b) for a in range(M.size) for b in range(M.size) if M.mul(a,b)==w.value}
    actual=set()
    for o,n in factor_structures(replace(w,value=0),i,j):
        for a in range(M.size):
            for b in range(M.size):
                outer=replace(o,value=a);inner=replace(n,value=b)
                es=tuple(inner if k==i else flat_identity(*p) for k,p in enumerate(outer.profile))
                if flat_compose(outer,es,M)==w:actual.add((outer,inner))
    assert actual==expected
    record('factorization_cases',(M.name,w.graph.n,len(w.blocks),i,j,len(actual)))
    COUNTS['factorization_fibre_elements']+=len(actual)

def run_F():
    expected=0
    for M in MONOIDS:
        for g in graphs(2):
            for n in (3,4):
                for a in range(3):
                    for b in range(a,3):
                        for w in catalog(g,Arrow(a,b),n,M):
                            for q in range(2,n):
                                for i in range(n-q+1):check_factor(w,i,i+q,M);expected+=1
        w=evaluation(six_term(M),M)
        for v in range(M.size):
            wv=replace(w,value=v)
            for q in (2,3):
                for i in range(4-q+1):check_factor(wv,i,i+q,M)
            for i,j in ((0,4),)+tuple((i,i+1) for i in range(4)):
                for a in range(M.size):
                    for b in range(M.size):
                        outer,inner=forced_factor(wv,i,j,a,b)
                        es=tuple(inner if k==i else flat_identity(*p) for k,p in enumerate(outer.profile))
                        assert (flat_compose(outer,es,M)==wv)==(M.mul(a,b)==v)
                        record('factor_full_unary_probes')
            objects=(wv.arrows[0].a,)+tuple(a.b for a in wv.arrows)
            for i in range(5):
                for a in range(M.size):
                    for b in range(M.size):
                        mid=Arrow(objects[i],objects[i]);inner=Flat(Graph(0),mid,(),(),b)
                        outer=Flat(wv.graph,wv.whole,wv.blocks[:i]+((),)+wv.blocks[i:],wv.arrows[:i]+(mid,)+wv.arrows[i:],a)
                        assert len(outer.blocks)==5 and outer!=wv
                        es=tuple(inner if k==i else flat_identity(*p) for k,p in enumerate(outer.profile))
                        assert (flat_compose(outer,es,M)==wv)==(M.mul(a,b)==v)
                        record('factor_empty_interval_probes')
        # Unary/full and nullary fibres are distinct labelled boundary probes.
        for a in range(3):
            for v in range(M.size):
                null=Flat(Graph(0),Arrow(a,a),(),(),v)
                assert evaluation(canonical(null,M),M)==null
                unary=replace(flat_identity(Graph(0),Arrow(a,a)),value=v)
                assert evaluation(canonical(unary,M),M)==unary and null!=unary
                for local in range(M.size):
                    target=flat_compose(unary,(replace(null,value=local),),M)
                    assert target==replace(null,value=M.mul(v,local))
                    record('unary_to_nullary_value_pairs')
                record('factor_boundary_probes')
    return expected


def main():
    start=time.monotonic();named_controls();print('named controls passed',flush=True)
    T=run_T();print('T passed',sum(r['executed'] for r in T),flush=True)
    run_X();print('X passed',flush=True)
    run_H();print('H passed',flush=True)
    F=run_F();print('F passed',F,flush=True)
    report={'status':'PASS','evidence':'C author redundancy, not independent review or unrestricted P/L','domain_sha256':hashlib.sha256((HERE/'DOMAIN.md').read_bytes()).hexdigest(),'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (HERE/'model.py',HERE/'check_integration.py')},'counts':dict(COUNTS),'T_rows':T,'F_exhaustive_cases':F,'trace_sha256':TRACE.hexdigest(),'elapsed_seconds':round(time.monotonic()-start,3),'limitations':['No categorical path congruence is defined by semantic equality.','Finite relation-path tests do not prove global ordinary or mixed coherence.','No novelty/scientific-scope acceptance inferred.']}
    (HERE/'AuthorCertificate.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
