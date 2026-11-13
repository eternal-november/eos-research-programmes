#!/usr/bin/env python3
"""Independently authored finite checks of actual I2 encoder/interpreter.
No imports of constructor partition routines. No infinite proof claim.
"""
import hashlib, importlib.util, itertools as it, json
from functools import lru_cache
from pathlib import Path
ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('candidate',ROOT/'verify_encoder_decoder.py')
C=importlib.util.module_from_spec(spec);spec.loader.exec_module(C)

def comp(f,g): return tuple(f[v] for v in g)
def closure(k):
    identity=tuple(range(k)); aa=(k-1,1)+tuple(range(1,k-1)); bb=(1,2)+(1,)*(k-2)
    # Right extension, rather than candidate's left extension.
    seen={identity}; frontier={identity}
    while frontier:
        nxt={comp(f,g) for f in frontier for g in (aa,bb)}-seen
        seen|=nxt;frontier=nxt
    return sorted(seen),identity,aa,bb

def partitions_from_cuts(vals,cuts,H):
    colors={x:int(x in H) for x in vals};rounds=0
    while True:
        signatures={x:(colors[x],frozenset((colors[a],colors[b]) for a,b in cuts[x])) for x in vals}
        lookup={s:i for i,s in enumerate(dict.fromkeys(signatures.values()))}
        refined={x:lookup[signatures[x]] for x in vals}
        if len(set(refined.values()))==len(set(colors.values())):return refined,rounds
        colors=refined;rounds+=1

def map_pair(enc,pair):return tuple(map(enc,pair))
def formula_checks(vals, codes, enc, concrete_mul, abstract_mul, concrete_obs, abstract_obs, transport):
    """Bounded independently evaluated generated AST bank, sourcewise joint cuts.
    State is ordered tuple; Cut consumes ONE outer and ONE ordered child tuple.
    Named skeleton Z is fixed, never a hidden observation or free witness field.
    """
    cache={}
    def concrete_cut(state):
        key=tuple(state)
        if key not in cache:
            rows=[]
            for p in vals:
                options=[[u for u in vals if concrete_mul(p,u)==x] for x in state]
                for children in it.product(*options):rows.append(((p,),children))
            cache[key]=rows
        return cache[key]
    def evaluate(ast,state,abstract=False):
        op=ast[0]
        obs=abstract_obs if abstract else concrete_obs
        mul=abstract_mul if abstract else concrete_mul
        if op=='atom':return obs(state[ast[1]])==ast[2]
        if op=='not':return not evaluate(ast[1],state,abstract)
        if op=='and':return all(evaluate(a,state,abstract) for a in ast[1:])
        if op in ('left','right'):
            fixed=enc(ast[1]) if abstract else ast[1]
            target=tuple(mul(fixed,x) if op=='left' else mul(x,fixed) for x in state)
            return evaluate(ast[2],target,abstract)
        if op=='swap':return evaluate(ast[1],tuple(transport(x) for x in state),abstract)
        if op=='cut':
            assert ast[1]=='fixed-old-skeleton/one-shared-parent'
            rows=(((a[0],),bs[0]) for a,bs in C.joint_cut(codes,abstract_mul,state,(len(state),))) if abstract else concrete_cut(state)
            return any(evaluate(ast[2],a,abstract) and evaluate(ast[3],b,abstract) for a,b in rows)
        raise AssertionError(op)
    atom=('atom',0,True);negative=('not',atom)
    cut=lambda a,b:('cut','fixed-old-skeleton/one-shared-parent',a,b)
    bank=[atom,negative,cut(atom,negative),cut(negative,negative),cut(negative,cut(negative,negative))]
    for fixed in vals[:3]+vals[-2:]:
        bank.extend([('left',fixed,cut(negative,negative)),('right',fixed,cut(atom,negative)),cut(atom,('left',fixed,negative))])
    bank.extend([('swap',atom),('swap',cut(atom,negative)),('and',atom,('not',cut(negative,negative)))])
    checks=0
    for rank in (1,2):
        rankbank=bank+([('atom',1,True),cut(atom,('and',atom,('not',('atom',1,True))))] if rank==2 else [])
        for state in it.product(vals,repeat=rank):
            encoded=tuple(map(enc,state))
            for ast in rankbank:
                assert evaluate(ast,state)==evaluate(ast,encoded,True)
                checks+=1
    return {'formula_source_evaluations':checks,'base_formula_count':len(bank),'rank2_extra_formulas':2,'max_tested_rank':2,'unbounded_claim':False}

def generic_checks():
    import finite_typed_realization as F
    vals,e,a,b=closure(4);sort='concrete-M4';nodes=[(sort,x) for x in vals]
    obs={n:n[1] in {e,b,comp(b,b)} for n in nodes}
    ops={(sort,('left',z)):{n:(sort,comp(z,n[1])) for n in nodes} for z in vals}
    ops.update({(sort,('right',z)):{n:(sort,comp(n[1],z)) for n in nodes} for z in vals})
    cuts={(sort,'joint'):{n:{((sort,u),(sort,v)) for u,v in it.product(vals,repeat=2) if comp(u,v)==n[1]} for n in nodes}}
    model=F.Model({sort:vals},obs,ops,cuts)
    q,quot,history,certificate=F.refine(model)
    assert len(set(q.values()))==10 and set(q.values())==quot.nodes
    for n in nodes:
        assert quot.obs[q[n]]==obs[n]
        for key,table in ops.items():assert quot.operations[key][q[n]]==q[table[n]]
        for key,table in cuts.items():assert set(quot.cuts[key][q[n]])=={tuple(q[y] for y in row) for row in table[n]}
    # Independent DAG interpreter with original concrete records; no constructor callback.
    @lru_cache(None)
    def holds(node,stage,code):
        if node[0]!=code[0]:return False
        if stage==0:return obs[node]==certificate.seed_definitions[code]
        old,ds,cs=certificate.definitions[stage-1][code]
        if not holds(node,stage-1,old):return False
        if any(not holds(ops[node[0],name][node],stage-1,target) for name,target in ds):return False
        earlier=certificate.seed_definitions if stage==1 else certificate.definitions[stage-2]
        for name,expected in cs:
            actual=set()
            for row in cuts[node[0],name][node]:
                options=[tuple(c for c in earlier if holds(y,stage-1,c)) for y in row]
                assert all(len(o)==1 for o in options)
                actual.update(it.product(*options))
            if actual!=set(expected):return False
        return True
    final=len(history)-1
    for n,c in it.product(nodes,quot.nodes):assert holds(n,final,c)==(q[n]==c)
    # Sensitivity: a corrupted observation decoder must fail equality.
    damaged=dict(quot.obs);first=next(iter(quot.nodes));damaged[first]=not damaged[first]
    assert any(damaged[q[n]]!=obs[n] for n in nodes)
    # Typed same-value occurrences and nullary set distinction survive constructor.
    tiny=F.Model({'A':(0,1),'B':(0,)},{('A',0):0,('A',1):0,('B',0):0},{},{('A','empty'):{('A',0):{()},('A',1):set()},('B','empty'):{('B',0):{()}}})
    tq,tr,_,_=F.refine(tiny)
    assert len(tr.nodes)==3 and tq['A',0]!=tq['B',0] and tq['A',0]!=tq['A',1]
    return {'original_nodes':10,'constructed_classes':10,'independent_DAG_truth_checks':100,'all_contexts':20,'nullary_typed_states':3,'damaged_decoder_detected':True}

def check():
    stats={'result':'PASS','scope':'finite coefficient checks; opaque exact old tags, not graph-engine validation','Mk':[]}
    for k in range(4,13):
        vals,e,a,b=closure(k); enc=lambda f:C.encode_m(k,f)
        assert len(vals)==3*k-2
        assert len(set(map(enc,vals)))==len(vals)
        assert all(C.decode_m(k,enc(f))==f for f in vals)
        cuts={x:[] for x in vals}
        for f,g in it.product(vals,repeat=2):
            fg=comp(f,g);cuts[fg].append((f,g))
            assert C.mul_m(k,enc(f),enc(g))==enc(fg)
        H={e,b,comp(b,b)}
        # H is a two-sided congruence; this finite law certifies arbitrary pure graft words.
        for f,g in it.product(vals,repeat=2):
            if (f in H)==(g in H):
                for z in vals:
                    assert (comp(z,f) in H)==(comp(z,g) in H)
                    assert (comp(f,z) in H)==(comp(g,z) in H)
        colors,rounds=partitions_from_cuts(vals,cuts,H)
        assert colors[e]==colors[b]
        for f,g in it.product(vals,repeat=2):
            assert (colors[f]==colors[g])==(enc(f)[1]==enc(g)[1])
        ae,ab=comp(a,e),comp(a,b)
        positive=lambda x:any(u not in H and v not in H for u,v in cuts[x])
        assert not positive(ae) and positive(ab)
        assert colors[ae]!=colors[ab] and (ae in H)==(ab in H)
        if k==4:
            # Validate recognizer rejection on EVERY transformation, not just members.
            for f in it.product(range(k),repeat=k):
                try:code=enc(f)
                except ValueError:assert f not in vals
                else:assert f in vals and C.decode_m(k,code)==f
            # Independently enumerate every common-parent factor triple once.
            shared={x:set() for x in it.product(vals,repeat=2)}
            for p,u,v in it.product(vals,repeat=3):
                shared[(comp(p,u),comp(p,v))].add(((enc(p),),((enc(u),enc(v)),)))
            codes=tuple(map(enc,vals))
            for source,expected in shared.items():
                actual=set(C.joint_cut(codes,lambda x,y:C.mul_m(k,x,y),tuple(map(enc,source)),(2,)))
                assert actual==expected
            # Both-channel graft and transport squares, no quotient formula reused.
            pairs=list(it.product(vals,repeat=2))
            for x,y in it.product(pairs,repeat=2):
                expected=tuple(enc(comp(xx,yy)) for xx,yy in zip(x,y))
                assert C.pair_mul(lambda u,v:C.mul_m(k,u,v),tuple(map(enc,x)),tuple(map(enc,y)))==expected
            for x in pairs:assert tuple(map(enc,(x[1],x[0])))==C.swap(tuple(map(enc,x)))
        stats['Mk'].append({'k':k,'concrete_states':len(vals),'product_checks':len(vals)**2,'pure_cut_refinement_rounds':rounds})
    G=list(it.product(range(4),repeat=2));Q=list(it.product(range(2),repeat=2))
    plus=lambda x,y:((x[0]+y[0])%4,(x[1]+y[1])%4)
    enc=C.group_encode
    assert set(map(enc,G))==set(Q)
    for x,y in it.product(G,repeat=2):
        assert enc(plus(x,y))==C.add(2)(enc(x),enc(y))
    for x in G:
        assert C.group_observe(enc(x))==x[0]%2
        assert C.swap(enc(x))==enc((x[1],x[0]))
    assert C.group_section(enc((3,2)))!=(3,2)
    # Direct concrete multiplication enumeration (not inverse lifting or candidate cut code).
    unary={x:set() for x in G}; shared={x:set() for x in it.product(G,repeat=2)}
    for p,u in it.product(G,repeat=2):unary[plus(p,u)].add(((enc(p),),((enc(u),),)))
    for p,u,v in it.product(G,repeat=3):
        shared[(plus(p,u),plus(p,v))].add(((enc(p),),((enc(u),enc(v)),)))
    for source,expected in unary.items():assert set(C.joint_cut(Q,C.add(2),(enc(source),),(1,)))==expected
    for source,expected in shared.items():
        actual=set(C.joint_cut(Q,C.add(2),tuple(map(enc,source)),(2,)))
        assert actual==expected
        for outer,inner in actual:assert C.graft(C.add(2),outer,inner)==tuple(map(enc,source))
    assert set(C.joint_cut(Q,C.add(2),(),()))=={((),())}
    # Profile and occurrence multiplicity are observable tags, not deduplicated labels.
    tag=('profile-A',('empty','active','empty','active'),'frame-A')
    x=(3,2);out=C.typed_encode(tag,(x,x),enc)
    assert out[0]==tag and out[1]==(enc(x),enc(x)) and len(out[1])==2
    assert out!=C.typed_encode(('profile-B',tag[1],tag[2]),(x,x),enc)
    stats['group']={'labels':16,'unary_sources':16,'shared_parent_rank2_sources':256,'concrete_factor_triples':4096,'compressed_states':4}
    v,e,a,b=closure(4);H={e,b,comp(b,b)}
    stats['mixed_ast_M4']=formula_checks(v,list(map(lambda x:C.encode_m(4,x),v)),lambda x:C.encode_m(4,x),comp,lambda x,y:C.mul_m(4,x,y),lambda x:x in H,lambda x:x[1]==0,lambda x:x)
    stats['mixed_ast_C4_squared']=formula_checks(G,Q,enc,plus,C.add(2),lambda x:bool(x[0]%2),lambda x:bool(C.group_observe(x)),C.swap)
    stats['Mk4']={'all_transformations_recognition':256,'shared_parent_rank2_sources':100,'two_channel_products':10000}
    # Original recursive positive-factor formulas, evaluated on concrete factor records.
    # Natural labels only tested below explicit finite bounds; no truncated saturation.
    nat={1:{n:n>0 for n in range(25)}}
    for m in range(2,13):nat[m]={n:any(a>0 and nat[m-1][n-a] for a in range(n+1)) for n in range(25)}
    for m,row in nat.items():assert all(value==(n>=m) for n,value in row.items())
    capcases=0
    for t in range(1,9):
        vals=range(t+1);cuts={n:[(a,b) for a,b in it.product(vals,repeat=2) if min(a+b,t)==n] for n in vals}
        truth={n:n>0 for n in vals}
        for m in range(1,13):
            assert all(truth[n]==(n>=min(m,t)) for n in vals)
            truth={n:any(a>0 and truth[b] for a,b in cuts[n]) for n in vals};capcases+=1
        # cap is a monoid map but fails sourcewise exact cut lifting at n=t.
        assert all(min(a+b,t)==min(min(a,t)+min(b,t),t) for a,b in it.product(range(2*t+2),repeat=2))
        projected={(min(a,t),min(t-a,t)) for a in range(t+1)}
        assert (t,t) in cuts[t] and (t,t) not in projected
    stats['boundary']={'natural_labels':25,'threshold_formulas':12,'cap_parameters':list(range(1,9)),'cap_formula_cases':capcases,'false_cutback_source':'n=t; abstract (t,t) cannot lift'}
    pins=['verify_encoder_decoder.py','encoder_decoder_draft.md','realization_theorem_draft.md','i2_minimal_realization_theorem.md','baseline_comparison.md']
    for optional in ['index_boundary_theorem.md','finite_typed_realization.py']:
        if (ROOT/optional).exists():pins.append(optional)
    stats['generic_constructor']=generic_checks()
    stats['source_sha256']={name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in pins}
    return stats
if __name__=='__main__':print(json.dumps(check(),indent=2,sort_keys=True))
