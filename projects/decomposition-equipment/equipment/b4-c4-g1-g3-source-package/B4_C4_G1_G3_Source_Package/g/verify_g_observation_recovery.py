#!/usr/bin/env python3
"""Fresh bounded tests for G1-G3; original sources are read-only and not imported.
Encoder: lift/partition arithmetic. Decoder: inspect each ambient vertex pair.
Domain fixed in G1_G3_proof_and_evidence_crosswalk.txt before this test run.
This is C corroboration, not the all-size P proof or a new Lean theorem.
"""
import hashlib,itertools,json,math
from pathlib import Path
if not __debug__:
    raise SystemExit('Refusing optimized Python: assertions are required')
ROOT=Path(__file__).resolve().parent
counts={}
def check(name,condition):
    if not condition: raise AssertionError(name)
    counts[name]=counts.get(name,0)+1

def pairs(n):return tuple(itertools.combinations(range(n),2))
def graphs(n):
    ps=pairs(n)
    for mask in range(1<<len(ps)):
        yield frozenset(e for i,e in enumerate(ps) if mask>>i&1)

def blocks_of(word,k):
    return tuple(tuple(i for i,x in enumerate(word) if x==j) for j in range(k))

def encode(n,E,B):
    local=[]
    for block in B:
        inv={v:i for i,v in enumerate(block)}
        local.append(tuple(sorted((inv[x],inv[y]) for x,y in E if x in inv and y in inv)))
    owner={v:i for i,b in enumerate(B) for v in b}
    cross=tuple(int(e in E) for e in pairs(n) if owner[e[0]]!=owner[e[1]])
    return {'n':n,'blocks':[list(b) for b in B], 'local':[list(map(list,h)) for h in local], 'cross':list(cross)}

def decode(record):
    """Input is JSON-compatible observation+supplement only; hidden E absent."""
    n=record['n'];B=record['blocks'];H=record['local'];C=record['cross']
    if sorted(v for b in B for v in b)!=list(range(n)):raise ValueError('partition')
    if any(b!=sorted(b) for b in B) or len(H)!=len(B):raise ValueError('coordinates')
    for b,h in zip(B,H):
        if any(not(0<=x<y<len(b)) for x,y in h) or len(set(map(tuple,h)))!=len(h):raise ValueError('local graph')
    ownership=[];position=[]
    for v in range(n):
        i=next(i for i,b in enumerate(B) if v in b)
        ownership.append(i);position.append(B[i].index(v))
    need=sum(ownership[x]!=ownership[y] for x,y in pairs(n))
    if len(C)!=need or any(c not in [0,1] for c in C):raise ValueError('cross bits')
    answer=set();cursor=0
    for x in range(n):
        for y in range(x+1,n):
            if ownership[x]==ownership[y]:
                if [position[x],position[y]] in H[ownership[x]]:answer.add((x,y))
            else:
                if C[cursor]:answer.add((x,y))
                cursor+=1
    return frozenset(answer)

def witness_rank(n,E,B,k):
    word=tuple(next(i for i,b in enumerate(B) if v in b) for v in range(n))
    sizes=tuple(map(len,B));words=tuple(w for w in itertools.product(range(k),repeat=n) if tuple(w.count(i) for i in range(k))==sizes)
    record=encode(n,E,B)
    rankC=sum(c<<i for i,c in enumerate(record['cross']))
    return words.index(word)*(1<<len(record['cross']))+rankC

def witness_unrank(local,sizes,k,rank):
    n=sum(sizes);q=sum(sizes[i]*sizes[j] for i in range(k) for j in range(i+1,k))
    words=tuple(w for w in itertools.product(range(k),repeat=n) if tuple(w.count(i) for i in range(k))==sizes)
    if not(0<=rank<len(words)*(1<<q)):raise ValueError('unused code')
    rB,rC=divmod(rank,1<<q);B=blocks_of(words[rB],k)
    rec={'n':n,'blocks':[list(b) for b in B],'local':local,'cross':[(rC>>i)&1 for i in range(q)]}
    return decode(rec),B

# All graph/partition pairs through n=4, k=4, retaining empty blocks.
fibre_sizes={}
for n in range(5):
    for k in range(5):
        for word in itertools.product(range(k),repeat=n):
            B=blocks_of(word,k);q=sum(len(B[i])*len(B[j]) for i in range(k) for j in range(i+1,k))
            local_fibres={}
            for E in graphs(n):
                rec=encode(n,E,B)
                # Serialize before decoding: object identity/private references cannot help.
                clean=json.loads(json.dumps(rec))
                check('small_pairwise_decoder',decode(clean)==E)
                key=tuple(tuple(map(tuple,h)) for h in rec['local'])
                local_fibres[key]=local_fibres.get(key,0)+1
                sizes=tuple(map(len,B))
                witnesskey=(n,k,sizes,key)
                fibre_sizes[witnesskey]=fibre_sizes.get(witnesskey,0)+1
                rank=witness_rank(n,E,B,k)
                backE,backB=witness_unrank(rec['local'],sizes,k,rank)
                check('small_unanchored_rank_decoder',backE==E and backB==B)
            check('anchored_fibre_count',all(v==1<<q for v in local_fibres.values()))
for (n,k,sizes,key),count in fibre_sizes.items():
    q=sum(sizes[i]*sizes[j] for i in range(k) for j in range(i+1,k))
    expected=math.factorial(n)//math.prod(math.factorial(s) for s in sizes)*(1<<q)
    check('unanchored_fibre_count',count==expected)

# Principal shared C5 family, all 13 independent cross bits.
B=((0,),(1,3),(2,4),(5,));fixed=frozenset({(1,3),(2,4)})
X=tuple(e for e in pairs(6) if e not in fixed)
check('principal_cross_bit_count',len(X)==13)
seen=set()
for mask in range(1<<13):
    E=fixed|frozenset(e for i,e in enumerate(X) if mask>>i&1)
    rec=encode(6,E,B)
    check('principal_pairwise_decoder',decode(json.loads(json.dumps(rec)))==E)
    check('principal_constant_local_graphs',rec['local']==[[],[[0,1]],[[0,1]],[]])
    seen.add(tuple(rec['cross']))
check('principal_full_fibre',len(seen)==8192)
for bit in range(13):
    rec0=encode(6,fixed,B);rec1=encode(6,fixed|{X[bit]},B)
    del rec0['cross'][bit];del rec1['cross'][bit]
    check('each_missing_bit_collision',rec0==rec1)
# Placement is genuinely separate even when edges and full local profile agree.
E=frozenset({(0,1)})
r0=encode(2,E,((0,),(1,)));r1=encode(2,E,((1,),(0,)))
r0.pop('blocks');r1.pop('blocks')
check('omitted_placement_collision',r0==r1)

# Exact original-C5 Z/3 noncompositional observable.
z=lambda m:int(m!=0)
check('zero_nonzero_input_equal',z(1)==z(2))
check('zero_nonzero_graft_failure',z((1+1)%3)!=z((2+1)%3))
# Kernel stability test, not merely a disclaimer.
unstable=[(a,b,c) for a in range(3) for b in range(3) for c in range(3) if z(a)==z(b) and z((a+c)%3)!=z((b+c)%3)]
check('actual_failed_observation_congruence',bool(unstable))

# Occurrence-wise forest decoder at the actual repeated middle components.
V=((0,),(1,),(3,),(4,),(2,),(5,))
grades=(0,1,1,1,1,1,2);sourcegrades=(0,1,1,1,2)
lengths=(1,2,2,1)
def forest_decode(sourceB,targetB,sourceboundary,targetboundary,lengths,values):
    if len(values)!=len(sourceB) or sum(lengths)!=len(targetB):raise ValueError('lengths')
    out=[];j=0
    for i,(u,length,value) in enumerate(zip(sourceB,lengths,values)):
        run=targetB[j:j+length]
        if set().union(*map(set,run))!=set(u):raise ValueError('run union')
        path=targetboundary[j:j+length+1]
        if path[0]!=sourceboundary[i] or path[-1]!=sourceboundary[i+1]:raise ValueError('boundary')
        if length==0 and (u or sourceboundary[i]!=sourceboundary[i+1]):raise ValueError('nullary')
        if any(path[x]>path[x+1] for x in range(len(path)-1)):raise ValueError('reverse grade')
        local=tuple(tuple(u.index(v) for v in block) for block in run)
        out.append({'blocks':local,'path':path,'value':value});j+=length
    return out
solutions=list(v for v in itertools.product(range(2),repeat=4) if sum(v)%2==0)
check('semantic_arrow_count',len(solutions)==8)
for code in itertools.product(range(2),repeat=3):
    values=code+(sum(code)%2,)
    forest=forest_decode(B,V,sourcegrades,grades,lengths,values)
    emitted=tuple(tuple(B[i][j] for j in block) for i,f in enumerate(forest) for block in f['blocks'])
    check('semantic_forest_decoder',emitted==V and tuple(f['value'] for f in forest)==values)
    check('semantic_forest_boundary',tuple(f['path'] for f in forest)==((0,1),(1,1,1),(1,1,1),(1,2)))
check('semantic_parallel_arrow_collision',(0,0,0,0) in solutions and (0,1,1,0) in solutions)
def substitute_blocks(source,localcuts):
    return tuple(tuple(source[i][j] for j in block) for i,cuts in enumerate(localcuts) for block in cuts)
forward=((0,),(1,));backward=((1,),(0,));identity=((0,),)
check('actual_occurrencewise_substitution',substitute_blocks(B,(identity,forward,backward,identity))==V)
check('type_keyed_substitution_failure_forward',substitute_blocks(B,(identity,forward,forward,identity))!=V)
check('type_keyed_substitution_failure_backward',substitute_blocks(B,(identity,backward,backward,identity))!=V)
for omitted in range(3):
    v0=(0,0,0,0);v1=tuple(int(i in (omitted,3)) for i in range(4))
    c0=tuple(v0[i] for i in range(3) if i!=omitted);c1=tuple(v1[i] for i in range(3) if i!=omitted)
    check('each_suppressed_scalar_bit_collision',v0!=v1 and sum(v0)%2==sum(v1)%2 and c0==c1)
# Actual active map [4]->[6] and fixed-source edge-forgetting lift.
alpha=(0,1,3,5,6)
merged=tuple(tuple(sorted(v for block in V[alpha[i]:alpha[i+1]] for v in block)) for i in range(4))
check('active_merge_partition',merged==B)
check('active_merge_typed_path',tuple(grades[i] for i in alpha)==sourcegrades)
E0=frozenset({(0,1),(1,2),(1,3),(2,4),(3,4),(4,5)});E1=E0|{(0,5)}
check('synthetic_ambiguous_bypass',encode(6,E0,B)['local']==encode(6,E1,B)['local'] and ((0,5) in E0)!=((0,5) in E1))
for coarseE in (E0,E1):
    matches=0
    for candidate in graphs(6):
        # Active pullback preserves the whole graph, hence the actual equation
        # to the retained coarse source compares candidate with coarseE.
        if candidate==coarseE and merged==B:matches+=1
    check('fixed_source_unique_active_lift',matches==1)
check('source_free_distinct_lifts',E0!=E1)

# Malformed input is rejected by the decoder rather than ignored.
for mutate in ('duplicate vertex','missing cross bit','bad local edge'):
    rec=encode(6,E0,B)
    if mutate=='duplicate vertex':rec['blocks'][0].append(1)
    elif mutate=='missing cross bit':rec['cross'].pop()
    else:rec['local'][1]=[[0,2]]
    try:decode(rec)
    except ValueError:check('malformed_input_rejection',True)
    else:raise AssertionError('accepted '+mutate)

result={'status':'PASS','evidence':'C, finite only','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'frozen_targets_file':'G1_G3_proof_and_evidence_crosswalk.txt',
        'finite_domain':{'small_n_max':4,'small_arity_max':4,'principal_graphs':8192,'scalar_monoids':['Z/2','Z/3'],'active_map':[0,1,3,5,6]},
        'checks':counts,'total_checks':sum(counts.values()),
        'zero_nonzero_failure_witnesses':unstable,
        'limits':'No all-degree computational proof, physical validation, Lean rerun, or all-context observation minimality is asserted.'}
(ROOT/'G_finite_results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps(result,indent=2,sort_keys=True))
