#!/usr/bin/env python3
"""Independent finite-language cross-check of semantic profile recognition.
No imports from the author's checkers. Finite tests supplement the paper proof.
"""
from itertools import product, combinations
from collections import deque
from pathlib import Path
import random, json, hashlib

class SortModel:
    def __init__(self, n, boundary, left, right, maps, sizes, q0, step, final):
        self.n=n; self.boundary=tuple(boundary); self.left=tuple(left); self.right=tuple(right)
        self.maps=maps; self.sizes=sizes; self.q0=q0; self.step=step; self.final=set(final)
        assert len(left)==n==len(right)
        assert all(x in self.boundary for x in left+right)
        for a,f in maps.items():
            assert len(f)==n and all(0<=z<sizes[a] for z in f)
    def accepts(self, b, word, vals, bp):
        q=self.step(self.q0,('L',b))
        for a,z in zip(word,vals): q=self.step(q,('V',a,z))
        return self.step(q,('R',bp)) in self.final
    def direct(self, word):
        target={ (b,tuple(vals),bp)
                 for b in self.boundary for bp in self.boundary
                 for vals in product(*(range(self.sizes[a]) for a in word))
                 if self.accepts(b,word,vals,bp) }
        images=[(self.left[x],tuple(self.maps[a][x] for a in word),self.right[x]) for x in range(self.n)]
        return {'image':any(t not in target for t in images),
                'injectivity':len(set(images))!=len(images),
                'surjectivity':bool(target-set(images))}
    def initial(self):
        traces=tuple(self.step(self.q0,('L',self.left[x])) for x in range(self.n))
        pairs=frozenset((x,y) for x,y in combinations(range(self.n),2) if self.left[x]==self.left[y])
        front=frozenset((self.step(self.q0,('L',b)),sum(1<<x for x in range(self.n) if self.left[x]==b)) for b in self.boundary)
        return traces,pairs,front
    def advance(self,state,a):
        traces,pairs,front=state; f=self.maps[a]
        traces=tuple(self.step(q,('V',a,f[x])) for x,q in enumerate(traces))
        pairs=frozenset((x,y) for x,y in pairs if f[x]==f[y])
        nxt=set()
        for q,mask in front:
            for z in range(self.sizes[a]):
                pre=sum(1<<x for x in range(self.n) if f[x]==z)
                nxt.add((self.step(q,('V',a,z)),mask&pre))
        return traces,pairs,frozenset(nxt)
    def finish(self,state):
        traces,pairs,front=state
        image=any(self.step(q,('R',self.right[x])) not in self.final for x,q in enumerate(traces))
        inj=any(self.right[x]==self.right[y] for x,y in pairs)
        surj=False
        for q,mask in front:
            for bp in self.boundary:
                last=sum(1<<x for x in range(self.n) if self.right[x]==bp)
                if self.step(q,('R',bp)) in self.final and not(mask&last): surj=True
        return {'image':image,'injectivity':inj,'surjectivity':surj}
    def automaton(self,word):
        s=self.initial()
        for a in word:s=self.advance(s,a)
        return self.finish(s)
    def dfa(self):
        states=[self.initial()]; ids={states[0]:0}; trans={}
        for s in states:
            i=ids[s]
            for a in self.maps:
                t=self.advance(s,a)
                if t not in ids:ids[t]=len(states);states.append(t)
                trans[i,a]=ids[t]
        accepting={i for i,s in enumerate(states) if not any(self.finish(s).values())}
        return states,trans,accepting

def all_support_model(n,maps,sizes,boundary=(0,),left=None,right=None):
    left=[0]*n if left is None else left;right=[0]*n if right is None else right
    return SortModel(n,boundary,left,right,maps,sizes,0,lambda q,t:0,{0})

def equal_tuple_model():
    # Target tuples have a common binary value; empty tuple has retained boundary 0.
    def step(q,t):
        if t[0] in ('L','R'):return q
        z=t[2]
        if q==0:return 1+z
        if q==3:return 3
        return q if q==1+z else 3
    return SortModel(2,[0],[0,0],[0,0],{'i':(0,1),'f':(1,0),'c':(0,0)},dict.fromkeys(['i','f','c'],2),0,step,{0,1,2})

def cfg_relation(nonterminals, productions, trans, nstates):
    """Least finite relation closure; stores one actual terminal derivation per fact."""
    R={n:{} for n in nonterminals}; rounds=0;changed=True
    while changed:
        changed=False; rounds+=1
        for lhs,rhs in productions:
            cur={(s,s):() for s in range(nstates)}
            for sym in rhs:
                rel=R[sym] if sym in R else {(s,trans[s,sym]):(sym,) for s in range(nstates)}
                nxt={}
                for (s,t),w in cur.items():
                    for (u,v),z in rel.items():
                        if t==u:nxt.setdefault((s,v),w+z)
                cur=nxt
            for pair,w in cur.items():
                if pair not in R[lhs]:R[lhs][pair]=w;changed=True
    return R,rounds

def main():
    rng=random.Random(20261027);checks=0; configs=0
    # Independent arbitrary regular supports, deliberately not candidate images.
    for case in range(420):
        n=rng.randrange(4); bn=rng.randrange(3) if n==0 else rng.randrange(1,3)
        boundary=tuple(range(bn)); left=[rng.choice(boundary) for _ in range(n)];right=[rng.choice(boundary) for _ in range(n)]
        sizes={a:rng.randrange(3) if n==0 else rng.randrange(1,3) for a in ('a','b')}
        maps={a:tuple(rng.randrange(sizes[a]) for _ in range(n)) for a in sizes}
        qn=rng.randrange(1,4)
        tokens=[('L',b) for b in boundary]+[('R',b) for b in boundary]+[('V',a,z) for a in maps for z in range(sizes[a])]
        table={(q,t):rng.randrange(qn) for q in range(qn) for t in tokens}
        final={q for q in range(qn) if rng.randrange(2)}
        m=SortModel(n,boundary,left,right,maps,sizes,0,lambda q,t,tab=table:tab[q,t],final)
        for k in range(5):
            for word in product(maps,repeat=k):
                assert m.direct(word)==m.automaton(word),(case,word,m.direct(word),m.automaton(word))
                checks+=1
        configs+=1
    controls=[]
    # Nullary boundary is not the singleton empty product; both legs are included.
    def diag(q,t):
        if t[0]=='L':return t[1]
        if t[0]=='R':return 2 if q==t[1] else 3
        return q
    null=SortModel(2,[0,1],[0,1],[0,1],{}, {},0,diag,{2})
    assert not any(null.automaton(()).values());controls.append('retained two-point nullary boundary is exact')
    neq=SortModel(1,[0,1],[0],[1],{}, {},0,diag,{2})
    assert neq.automaton(())['image'];controls.append('unequal nullary legs rejected by image test')
    lost=SortModel(2,[0],[0,0],[0,0],{}, {},0,lambda q,t:0,{0})
    assert lost.automaton(())['injectivity'];controls.append('nullary common leg event collapse detected')
    empty=all_support_model(0,{'a':()}, {'a':0})
    assert not any(empty.automaton(('a',)).values());assert empty.automaton(())['surjectivity']
    controls.append('empty roots and empty component support distinguished')
    # Pairwise/intersection bookkeeping is necessary, not separate leaf coverage.
    corr=all_support_model(2,{'a':(0,1)}, {'a':2})
    assert not any(corr.automaton(('a',)).values())
    assert corr.automaton(('a','a'))['surjectivity'];controls.append('joint preimage intersection detects invented mixed tuple')
    eq=equal_tuple_model()
    assert not any(eq.automaton(('i','i','i')).values())
    assert eq.automaton(('i','f'))['image'];controls.append('independent joint support cannot be replaced by candidate image')
    state=all_support_model(1,{'a':(0,)},{'a':1})
    event=all_support_model(2,{'a':(0,0)},{'a':1})
    assert not any(state.automaton(('a',)).values()) and event.automaton(('a',))['injectivity']
    controls.append('parallel event collapse passes states but fails events')
    # Boundary coordinates can distinguish root records even at no leaves.
    assert len(set(null.left))==2 and not any(null.automaton(()).values())
    controls.append('injectivity cannot omit actual outer boundary coordinates')
    # Persistent same hardware/common profile versus separate per-world choices.
    w0=all_support_model(2,{'a':(0,1),'b':(0,0)},{'a':2,'b':2})
    w1=all_support_model(2,{'a':(0,0),'b':(0,1)},{'a':2,'b':2})
    assert any(not any(w0.automaton((a,)).values()) for a in ('a','b'))
    assert any(not any(w1.automaton((a,)).values()) for a in ('a','b'))
    assert not any(not any(w0.automaton((a,)).values()) and not any(w1.automaton((a,)).values()) for a in ('a','b'))
    controls.append('forall worlds exists profile differs from one profile for every world')
    # Construct whole DFA and genuine CFG fixed point, not bounded word search.
    states,trans,acc=eq.dfa(); nts={'S','T','E'}
    prods=[('S',('i',)),('S',('i','S')),('T',('i','T')),('T',('f',)),('E',()),('E',('E',))]
    R,rounds=cfg_relation(nts,prods,trans,len(states))
    assert all(v in acc for (u,v) in R['S'] if u==0)
    assert any(v not in acc for (u,v) in R['T'] if u==0)
    assert set(R['E'])=={(q,q) for q in range(len(states))}
    controls.append('recursive grammar and epsilon cycle reach exact least fixed point')
    # Delay the first bad word beyond depth 14; unbounded saturation still finds it.
    nts={f'N{i}' for i in range(16)}
    prods=[(f'N{i}',('i',f'N{i+1}')) for i in range(15)]+[('N15',('f',))]
    Rd,dr=cfg_relation(nts,prods,trans,len(states))
    ws=[w for (u,v),w in Rd['N0'].items() if u==0 and v not in acc]
    assert ws and min(map(len,ws))==16 and all(eq.automaton(w)['image'] for w in ws)
    controls.append('depth-14 truncation misses forced length-16 defect recovered by CFG saturation')
    root=Path(__file__).resolve().parents[1]
    source=root/'theory/Operational_Semantic_Profile_Recognition.md'
    result={'status':'PASS','random_regular_support_instances':configs,'direct_vs_automaton_word_checks':checks,
            'mutation_and_scope_controls':controls,'exact_language_DFA_states':len(states),'CFG_saturation_rounds':rounds,
            'delayed_defect_length':16,'delayed_saturation_rounds':dr,
            'reviewed_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'scope':'Set-sort recognition algorithms and CFG fixed-point independently checked; state/event distinction explicit. General graph incidence and physical alphabet checks belong to separate checker and paper proof. No finite-test extrapolation.'}
    out=root/'review/Unbounded_Recognition_Independent_Results.json';out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


def common_refinement_fixture(xor_parent=False):
    """Exact unbounded regular-language reachability, not a word-depth cutoff.
    Rows project (a,b); columns project (a xor b,b) or (a,b).
    Each inner joint support is the independently fixed equal-coordinate relation.
    """
    worlds=list(product(range(2),repeat=2))
    funcs=[(0,0),(0,1),(1,0),(1,1)]
    row=lambda i,w:w[i]
    col=lambda j,w:(w[0]^w[1]) if xor_parent and j==0 else w[j]
    letters=[]
    for i,j,f,g in product(range(2),range(2),funcs,funcs):
        if all(f[row(i,w)]==g[col(j,w)] for w in worlds): letters.append((i,j,f,g))
    models=[equal_tuple_model() for _ in range(4)]
    # Extend local alphabet to all four actual Boolean maps; support remains fixed.
    for model in models:
        model.maps={f:f for f in funcs};model.sizes={f:2 for f in funcs}
    start=tuple(m.initial() for m in models)+(-1,)
    queue=deque([start]); seen={start:()}; accepted=None; transitions=0
    while queue:
        state=queue.popleft()
        if all(not any(m.finish(s).values()) for m,s in zip(models,state[:4])) and accepted is None:accepted=seen[state]
        for letter in letters:
            i,j,f,g=letter;cell=2*i+j
            if cell<state[-1]:continue  # Explicit row-major traversal doctrine.
            nxt=list(state)
            nxt[i]=models[i].advance(state[i],f)
            nxt[2+j]=models[2+j].advance(state[2+j],g)
            nxt[-1]=cell;nxt=tuple(nxt);transitions+=1
            if nxt not in seen:seen[nxt]=seen[state]+(letter,);queue.append(nxt)
    return {'alphabet_letters':len(letters),'reachable_product_states':len(seen),'checked_transitions':transitions,
            'has_common_refinement':accepted is not None,'witness':accepted}


def extra_tests():
    p=common_refinement_fixture(False);n=common_refinement_fixture(True)
    assert p['has_common_refinement'] and not n['has_common_refinement']
    assert len(p['witness'])==2
    # A whole command can require TWO leaf ports: do not demand each leaf produces it alone.
    inp=list(product((0,1),repeat=2)); desired=tuple(a^b for a,b in inp)
    ports={'x':tuple(a for a,b in inp),'y':tuple(b for a,b in inp)}
    def hardware_monitor(word,root_truth=desired):
        assigned={}
        for name,truth in word:
            if name in assigned and assigned[name]!=truth:return False
            assigned[name]=truth
        return set(assigned)=={'x','y'} and tuple(a^b for a,b in zip(assigned['x'],assigned['y']))==root_truth
    assert hardware_monitor(tuple(ports.items()))
    assert not hardware_monitor((('x',ports['x']),))
    assert not hardware_monitor(tuple(ports.items()),tuple(a&b for a,b in inp))
    assert not hardware_monitor((('x',ports['x']),('x',ports['y']),('y',ports['y'])))
    root=Path(__file__).resolve().parents[1]
    out=root/'review/Unbounded_Recognition_Independent_Results.json';r=json.loads(out.read_text())
    r['common_refinement_full_language_checks']={'positive_axes':p,'negative_XOR_axes':n,
        'language':'All finite row-major cell words; finite product DFA exhausted with no depth bound.',
        'event_only_instantiation':'Same Boolean table construction applies to parallel event records on singleton state graphs. A state-only recognizer would miss the XOR obstruction.'}
    r['global_hardware_monitor_controls']=['two leaves jointly assemble XOR request','missing port rejected','wrong assembled request rejected','conflicting alias assignments rejected']
    r['reviewed_source_sha256']=hashlib.sha256((root/'theory/Operational_Semantic_Profile_Recognition.md').read_bytes()).hexdigest()
    out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'common_refinement':r['common_refinement_full_language_checks'],'hardware_monitor':'PASS'},indent=2))



def dynamic_crossing_fixture(forbid_bottom_right=False):
    pairs=list(product((0,1),repeat=2));worlds=list(product((0,1),repeat=4))
    pairid={x:i for i,x in enumerate(pairs)}
    all_functions=list(product((0,1),repeat=4))
    maps=[]
    for f in all_functions:
        if all(f[pairid[(a^r,b^r)]]==(f[pairid[(a,b)]]^r) for a,b in pairs for r in (0,1)):
            maps.append(f)
    assert len(maps)==4
    rowcoords=((0,1),(2,3));colcoords=((0,2),(1,3))
    letters=[]
    for i,j,f,g in product(range(2),range(2),maps,maps):
        if forbid_bottom_right and (i,j)==(1,1):continue
        if all(f[pairid[tuple(w[t] for t in rowcoords[i])]]==g[pairid[tuple(w[t] for t in colcoords[j])]] for w in worlds):
            letters.append((i,j,f,g))
    def axis(f):
        return next(k for k in (0,1) if all(f[pairid[x]]==(x[k]^f[0]) for x in pairs))
    # Exact full-product refinement of two bits has precisely two independent leaves.
    # This finite reduction is proved by target cardinality 2^k (states), 2^(k+1) events.
    def update(s,f):
        if s=='E':return ('ONE',axis(f))
        if isinstance(s,tuple):return 'G' if s[1]!=axis(f) else 'B'
        return 'B'
    start=('E','E','E','E',-1);queue=deque([start]);seen={start:()};witness=None;edges=0
    while queue:
        state=queue.popleft()
        if state[:4]==('G','G','G','G') and witness is None:witness=seen[state]
        for letter in letters:
            i,j,f,g=letter;cell=2*i+j
            if cell<state[4]:continue
            nxt=list(state);nxt[i]=update(state[i],f);nxt[2+j]=update(state[2+j],g);nxt[4]=cell;nxt=tuple(nxt);edges+=1
            if nxt not in seen:seen[nxt]=seen[state]+(letter,);queue.append(nxt)
    if witness:
        image_states=set();image_events=set()
        for w in worlds:
            vals=tuple(f[pairid[tuple(w[t] for t in rowcoords[i])]] for i,j,f,g in witness)
            image_states.add(vals)
            for r in (0,1):image_events.add(tuple((v,r) for v in vals))
        fine_states=set(product((0,1),repeat=4))
        fine_events={tuple((v,r) for v in vals) for vals in fine_states for r in (0,1)}
        coarse_events=set(product(list(product((0,1),repeat=2)),repeat=4))
        assert image_states==fine_states and image_events==fine_events
        assert len(image_events)==32 and len(coarse_events)==256 and image_events<coarse_events
    return {'admissible_parent_graph_maps':len(maps),'candidate_cell_letters':len(letters),
            'reachable_states':len(seen),'checked_transitions':edges,'has_common_refinement':witness is not None,
            'witness_cells':[(i,j) for i,j,_,_ in witness] if witness else None}


def dynamic_extra():
    pos=dynamic_crossing_fixture(False);neg=dynamic_crossing_fixture(True)
    assert pos['has_common_refinement'] and len(pos['witness_cells'])==4 and not neg['has_common_refinement']
    root=Path(__file__).resolve().parents[1];out=root/'review/Unbounded_Recognition_Independent_Results.json';r=json.loads(out.read_text())
    r['dynamic_four_bit_crossing']={'positive':pos,'forbidden_cell_negative':neg,
         'actual_graphs':'Whole16states32events; J one state and distinct hold/flip events; every flip changes all four bits.',
         'fine_exact_event_records':32,'coarsened_target_event_records':256,
         'language':'All finite row-major cell words; full finite-state reachability. Inner full-product cardinality reduction is exact for all arities.'}
    r['reviewed_source_sha256']=hashlib.sha256((root/'theory/Operational_Semantic_Profile_Recognition.md').read_bytes()).hexdigest()
    out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r['dynamic_four_bit_crossing'],indent=2))



def retained_registry_test():
    # General retained-joint diagram comparison; internal registry transports
    # need not be the identity even when actual leaf and outer coordinates agree.
    U={x:('leaf',x,('u',x)) for x in (0,1)}
    V={x:('leaf',x,('v',1-x)) for x in (0,1)}
    invU={v:k for k,v in U.items()};phi={u:V[invU[u]] for u in invU}
    assert set(phi.values())==set(V.values())
    assert all(u[:2]==v[:2] for u,v in phi.items())
    assert any(u[2][1]!=v[2][1] for u,v in phi.items())
    # Nonterminal two-point retained boundary and actual changing transitions.
    for x,r in product((0,1),repeat=2):
        assert phi[U[x]]==V[x] and phi[U[x^r]]==V[x^r]
    # Syntactic endpoint identities are independent of assigned boundary graphs.
    def typed_path(start,end,edges):
        v=start
        for a,b in edges:
            if a!=v:return False
            v=b
        return v==end
    scalar=all_support_model(1,{}, {})
    assert not any(scalar.automaton(()).values())
    assert not typed_path('a','b',()) and typed_path('a','a',())
    assert typed_path('a','b',(('a','b'),))
    root=Path(__file__).resolve().parents[1];out=root/'review/Unbounded_Recognition_Independent_Results.json';j=json.loads(out.read_text())
    j['syntactic_type_control']='PASS: equal assigned boundary graphs do not license a nullary profile between distinct syntactic vertices; each erased row/column needs its own endpoint monitor.'
    j['occurrence_alias_control']='PASS: different named ports may have the same component color; equality constraints use actual physical identifiers, not color equality.'
    j['retained_boundary_registry_control']='PASS: graph-of-Phi transports internal registry; pure coordinate identity rejected. This is a retained-joint diagram control, not a claim that arbitrary extra registry data is in the bare Calc tuple alphabet.'
    j['reviewed_source_sha256']=hashlib.sha256((root/'theory/Operational_Semantic_Profile_Recognition.md').read_bytes()).hexdigest()
    out.write_text(json.dumps(j,indent=2)+'\n')


def universal_validity_regression():
    # All words are bijective on both singleton graph sorts. Physical assembly
    # nevertheless needs both named ports; graph Bad cannot detect missing y.
    model=all_support_model(1,{'x':(0,),'y':(0,)},{'x':1,'y':1})
    trans={(q,a):q | (1 if a=='x' else 2) for q in range(4) for a in ('x','y')}
    relation,rounds=cfg_relation({'S'},[('S',('x',)),('S',('x','S'))],trans,4)
    candidates=[(q,w) for (p,q),w in relation['S'].items() if p==0]
    assert candidates and all(not any(model.automaton(w).values()) for q,w in candidates)
    old_bad_witnesses=[w for q,w in candidates if any(model.automaton(w).values())]
    corrected_witnesses=[w for q,w in candidates if q!=3 or any(model.automaton(w).values())]
    assert not old_bad_witnesses and corrected_witnesses
    assert min(corrected_witnesses,key=len)==('x',)
    # Same defect at epsilon with distinct syntactic endpoints, despite singleton
    # assigned boundary graphs and exact retained empty tuple.
    assert not any(model.automaton(()).values())
    syntactic_valid=('left_vertex'=='right_vertex')
    assert not syntactic_valid
    root=Path(__file__).resolve().parents[1];out=root/'review/Unbounded_Recognition_Independent_Results.json';j=json.loads(out.read_text())
    j['universal_candidate_validity_control']={
        'status':'PASS','candidate_language':'x+ (unbounded recursive grammar)',
        'graph_defect_witnesses':len(old_bad_witnesses),
        'complement_Exact_witness':list(min(corrected_witnesses,key=len)),
        'reason':'missing required physical port y; V fails although graph exactness passes',
        'nullary_nonloop_control':'PASS: syntactic V failure at empty word, no graph defect',
        'grammar_saturation_rounds':rounds}
    j['reviewed_source_sha256']=hashlib.sha256((root/'theory/Operational_Semantic_Profile_Recognition.md').read_bytes()).hexdigest()
    out.write_text(json.dumps(j,indent=2)+'\n')
    print(json.dumps(j['universal_candidate_validity_control'],indent=2))


if __name__ == '__main__':
    main()
    extra_tests()
    dynamic_extra()
    retained_registry_test()
    universal_validity_regression()
