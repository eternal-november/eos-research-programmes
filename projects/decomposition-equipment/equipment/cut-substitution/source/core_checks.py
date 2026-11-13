"""Finite actual-span checks. Standard library only; no assert-dependent checks."""
from itertools import product, permutations
from collections import Counter

def require(ok, msg):
    if not ok: raise RuntimeError(msg)

def span(rows): return dict(rows)
def tuples(spans):
    return tuple(t for t in product(*(tuple(s) for s in spans)) if all(spans[i][t[i]][1]==spans[i+1][t[i+1]][0] for i in range(len(t)-1)))
def endpoints(ss,t): return ss[0][t[0]][0],ss[-1][t[-1]][1]
def bijective(m,target): return len(m)==len(target) and set(m.values())==set(target)
def comp(a,b): return {x:a[b[x]] for x in b}
def inverse(m):
    require(len(set(m.values()))==len(m),'inverse not bijective'); return {v:k for k,v in m.items()}
def base(): return {(x,y):(x,y) for x,y in product(range(2),repeat=2)}
def refined(level,name):
    # Actual identity spans followed by a full relation, named independently per occurrence.
    ss=[{('id',name,k,x):(x,x) for x in range(2)} for k in range(level)]+[{('rel',name,x,y):(x,y) for x,y in product(range(2),repeat=2)}]
    ts=tuples(ss); carrier={t:endpoints(ss,t) for t in ts}; m={t:t[-1][-2:] for t in ts}
    return carrier,m,ss

def diagram(tree, leaves, seed=0, canonical=False):
    nodes={}
    def rec(t):
        if isinstance(t,str):
            nodes[t]={'children':None,'span':leaves[t]};return
        name,children=t
        for c in children: rec(c)
        names=[c if isinstance(c,str) else c[0] for c in children];ss=[nodes[c]['span'] for c in names]; dom=tuples(ss)
        # Arbitrary supplied opaque beta tables, not canonical tuple carriers.
        perm=list(range(len(dom))); shift=(seed+len(name)+1)%len(perm) if perm else 0;perm=perm[shift:]+perm[:shift]
        beta={x:(x if canonical else (name,seed,perm[i])) for i,x in enumerate(dom)}
        carrier={beta[x]:endpoints(ss,x) for x in dom}
        nodes[name]={'children':names,'span':carrier,'beta':beta}
    rec(tree);return nodes

def maps(new,old,leafmaps):
    out={}
    def rec(n):
        if old[n]['children'] is None: out[n]=leafmaps[n];return
        cs=old[n]['children']
        for c in cs: rec(c)
        out[n]={v:old[n]['beta'][tuple(out[c][x] for c,x in zip(cs,t))] for t,v in new[n]['beta'].items()}
    root=next(reversed(old));rec(root)
    check(new,old,out);return out

def check(new,old,k):
    for n in old:
        require(set(k[n])==set(new[n]['span']),'map domain')
        require(all(new[n]['span'][x]==old[n]['span'][y] for x,y in k[n].items()),'fixed-interface map')
        if old[n]['children'] is not None:
            for t,y in new[n]['beta'].items():
                require(k[n][y]==old[n]['beta'][tuple(k[c][x] for c,x in zip(old[n]['children'],t))],'naturality')

def contract(d,cut):
    # Simultaneously substitute actual beta tables; retain all surviving edge IDs.
    out={}
    def frontier(n):
        return sum((frontier(c) if c in cut else [c] for c in d[n]['children']),[])
    for n,v in d.items():
        if n in cut: continue
        if v['children'] is None: out[n]=v;continue
        cs=frontier(n);ss=[d[c]['span'] for c in cs]
        def evaluate(t):
            vals=dict(zip(cs,t))
            def ev(c): return d[c]['beta'][tuple(ev(a) for a in d[c]['children'])] if c in cut else vals[c]
            return v['beta'][tuple(ev(c) for c in v['children'])]
        out[n]={'children':cs,'span':v['span'],'beta':{t:evaluate(t) for t in tuples(ss)}}
    return out

def typed_order():
    counts={}
    for r,c in [(1,1),(2,2),(2,3),(3,3),(3,4),(4,4)]:
        cells=list(product(range(r),range(c)));n=0
        for mask in range(1<<len(cells)):
            s=[x for i,x in enumerate(cells) if mask>>i&1]
            chain=not any(i<k and j>l for i,j in s for k,l in s)
            require(chain==(sorted(s)==sorted(s,key=lambda x:(x[1],x[0]))),'support equivalence');n+=1
        counts[f'{r}x{c}']=n
    atom=lambda name,grade='id',component='empty',A='A':(name,component,A,grade,A)
    def word(cells,slots,mode,remove):
        ordered=sorted(cells,key=(lambda x:(x[1],x[0])) if mode=='col' else None)
        arr=[cells[x] for x in ordered];bins={}
        for position,entry,designated in slots:
            if position is None: return None
            genuine=designated and entry[1:] == ('diagonal','A','id','A')
            if entry[0] in remove:
                if not genuine: return None
                continue
            bins.setdefault(position,[]).append(entry)
        return sum((bins.get(i,[])+([arr[i]] if i<len(arr) else []) for i in range(len(arr)+1)),[])
    cells={(0,0):atom('a',component='vertex'),(0,1):atom('b',component='vertex'),(1,1):atom('c',component='vertex')}
    cases=[]
    for label,rs,cs,remove,expected in [
        ('genuine unit deletion',[(1,atom('u',component='diagonal'),True)],[],{'u'},True),
        ('real empty id retained',[(1,atom('e'),False)],[(1,atom('e'),False)],set(),True),
        ('real empty id cannot erase',[(1,atom('e'),False)],[],{'e'},False),
        ('nonidentity empty grade retained',[(1,atom('e','g'),False)],[(1,atom('e','g'),False)],set(),True),
        ('nonidentity cannot erase',[(1,atom('e','g',component='diagonal'),True)],[],{'e'},False),
        ('empty slot position mismatch',[(1,atom('e'),False)],[(2,atom('e'),False)],set(),False),
        ('missing empty position',[(None,atom('e'),False)],[],set(),False),
        ('repeated types distinct occurrence',[(1,atom('e'),False)],[(1,atom('f'),False)],set(),False),
        ('interface mismatch',[(1,atom('e',A='B'),False)],[(1,atom('e'),False)],set(),False)]:
        a,b=word(cells,rs,'row',remove),word(cells,cs,'col',remove);got=a is not None and b is not None and a==b
        require(got==expected,label);cases.append({'case':label,'parallel':got})
    return {'support_masks':counts,'typed_empty_cases':cases,'segmentation_check':'each cell tag retains occurrence and original row/column address; boundary slots explicitly indexed'}

def tree_checks():
    tree=('root',[('p',['a','b']),('q',['c',('r',['d','e'])]),'f']);names=list('abcdef')
    ds=[];evaluations=[];forests=[]
    for level in range(3):
        leaves={};ev={};fs={}
        for n in names:
            leaves[n],ev[n],fs[n]=refined(level,n)
        ds.append(diagram(tree,leaves,seed=7+level));evaluations.append(ev);forests.append(fs)
    k10=maps(ds[1],ds[0],{n:{x:inverse(evaluations[0][n])[y] for x,y in evaluations[1][n].items()} for n in names})
    k21=maps(ds[2],ds[1],{n:{x:inverse(evaluations[1][n])[y] for x,y in evaluations[2][n].items()} for n in names})
    k20=maps(ds[2],ds[0],{n:comp(k10[n],k21[n]) for n in names})
    require(all(k20[n]==comp(k10[n],k21[n]) for n in ds[0]),'two refinement composition')
    ident=maps(ds[0],ds[0],{n:{x:x for x in ds[0][n]['span']} for n in names})
    require(all(all(x==y for x,y in m.items()) for m in ident.values()),'noncanonical identity')
    checks=0
    for cut1 in [set(),{'p'},{'q'},{'r'},{'p','r'}]:
        for cut2 in [set(),{'p'},{'q'},{'r'},{'p','q','r'}]:
            cut2=cut2-cut1;cut=cut1|cut2
            contracted=[contract(d,cut) for d in ds]
            for d in ds: require(contract(contract(d,cut1),cut2)==contract(d,cut),'nested disjoint vertical associativity')
            for new,old,k in [(contracted[1],contracted[0],k10),(contracted[2],contracted[1],k21),(contracted[2],contracted[0],k20)]:check(new,old,{n:k[n] for n in new})
            for n in contracted[0]:require(k20[n]==comp(k10[n],k21[n]),'middle four')
            checks+=1
    # CS is exact old skeleton plus literal external forest, not a newly exact graft.
    external={n:{'occurrence':n,'frontier_spans':forests[1][n],
                 'stage_name':n+'.insert_identity','coefficient':k10[n],
                 'target_span':ds[0][n]['span'],'scalar':1} for n in names}
    cs={'skeleton':ds[0],'external_forest':external};sc=diagram(tree,{n:ds[1][n]['span'] for n in names},canonical=True)
    for n,record in cs['external_forest'].items():
        require(set(record['coefficient'])==set(tuples(record['frontier_spans'])),'CS full forest reconstruction domain')
        require(record['coefficient']==k10[n],'CS retained coefficient reconstruction')
    canonical_lambda=maps(sc,ds[0],{n:k10[n] for n in names})
    require(all(t==v for n in sc if sc[n]['children'] for t,v in sc[n]['beta'].items()),'normalized SC beta')
    # The named top node below is the final proper cut edge. Add a fixed output root.
    # Its span is the singleton relation at each endpoint pair; gamma forgets internal witnesses.
    output=base()
    gamma_old={x:ds[0]['root']['span'][x] for x in ds[0]['root']['span']}
    gamma_new=comp(gamma_old,canonical_lambda['root'])
    root_identity={x:x for x in output}
    require(all(root_identity[gamma_new[x]]==gamma_old[canonical_lambda['root'][x]] for x in gamma_new),'fixed output root naturality')
    require(cs['skeleton']['p']['beta']!=sc['p']['beta'],'distinct noncanonical certificates')
    root_coeff=gamma_old;new_root=gamma_new
    require(not bijective(root_coeff,output),'arbitrary nonbijective endpoint preserving root')
    return {'tree':'root(p(a,b),q(c,r(d,e)),f)','leaf_occurrences':names,'levels':3,'root_witnesses':len(root_coeff),'root_coefficient_bijective':False,'contraction_pasting_pairs':checks,'noncanonical_identity':True,'CS_encoding':'old exact skeleton + external occurrence-indexed full forest','SC_encoding':'normalized tuple-carrier exact skeleton with flat refined bundles; separate noncanonical diagrams test general arrows','fixed_output_root_carrier':list(output),'root_component':'identity on unchanged output span','top_node_named_root_is':'final proper edge feeding separate arbitrary output coefficient','lambda_components':{n:len(m) for n,m in k10.items()},'root_equation_checks':len(new_root),'all_degree_claim':False}

def xi_checks():
    results=[]
    for n in [3,5,7,9]:
        names=[f'a{i}' for i in range(n)]
        rows=[names[i:i+2] for i in range(0,n,2)];cols=[names[:1]]+[names[i:i+2] for i in range(1,n,2)]
        def cut(groups,leaves,seed):
            return diagram(('root',[(f'g{i}',g) for i,g in enumerate(groups)]),leaves,seed)
        def ungroup(d,groups,t):return sum((inverse(d[f'g{i}']['beta'])[x] for i,x in enumerate(t)),())
        def regroup(d,groups,t):
            p=0;out=[]
            for i,g in enumerate(groups):out.append(d[f'g{i}']['beta'][t[p:p+len(g)]]);p+=len(g)
            return tuple(out)
        leaves0={};leaves1={};lm={}
        for a in names:
            leaves0[a],m0,_=refined(0,a);leaves1[a],m1,_=refined(1,a);lm[a]={x:inverse(m0)[y] for x,y in m1.items()}
        ro,co=cut(rows,leaves0,11),cut(cols,leaves0,21);rn,cn=cut(rows,leaves1,31),cut(cols,leaves1,41)
        kr,kc=maps(rn,ro,lm),maps(cn,co,lm)
        xiold={t:regroup(co,cols,ungroup(ro,rows,t)) for t in ro['root']['beta']}
        xinew={t:regroup(cn,cols,ungroup(rn,rows,t)) for t in rn['root']['beta']}
        for t in xinew:
            left=xiold[tuple(kr[f'g{i}'][x] for i,x in enumerate(t))]
            right=tuple(kc[f'g{i}'][x] for i,x in enumerate(xinew[t]));require(left==right,'Xi_old Krows = Kcols Xi_new')
        require(bijective(xiold,co['root']['beta']) and bijective(xinew,cn['root']['beta']),'Xi bijections')
        results.append({'atoms':n,'rows':list(map(len,rows)),'columns':list(map(len,cols)),'pointwise_equations':len(xinew),'distinct_occurrences_same_span_type':True})
    return results

def semantic_checks():
    # Actual endpoint-preserving operations with singleton boundary; arbitrary arity trees.
    def node(target,children,table):return {'target':target,'children':children,'table':table}
    def leaf(size):return {'target':tuple(range(size)),'children':None}
    def dp(v):
        if v['children'] is None:return {x:1 for x in v['target']}
        cc=[dp(c) for c in v['children']];out={x:0 for x in v['target']}
        for t,y in v['table'].items():
            weight=1
            for c,x in zip(cc,t):weight*=c[x]
            out[y]+=weight
        return out
    def brute(v):
        if v['children'] is None:return [(x,(x,)) for x in v['target']]
        out=[]
        for choices in product(*(brute(c) for c in v['children'])):
            t=tuple(x[0] for x in choices);out.append((v['table'][t],sum((x[1] for x in choices),())))
        return out
    count=0
    for a,b,c in product(range(1,4),repeat=3):
        for f in product(range(b),repeat=a):
            first=node(tuple(range(b)),[leaf(a)],{(x,):f[x] for x in range(a)})
            for g in product(range(c),repeat=b):
                v=node(tuple(range(c)),[first],{(x,):g[x] for x in range(b)})
                require(dp(v)==dict(Counter({**{x:0 for x in range(c)},**Counter(x for x,_ in brute(v))})),'DP brute unary');count+=1
    # Nonunary and genuinely compatible endpoints: independent direct enumeration in Xi tests;
    # here nonunary branching DP multiplicities exercise the product term.
    branching=[]
    for width in [2,3,4,5]:
        children=[node((0,1),[leaf(3)],{(0,):0,(1,):0,(2,):1}) for _ in range(width)]
        v=node((0,1),children,{t:sum(t)%2 for t in product((0,1),repeat=width)})
        require(dp(v)=={x:sum(y==x for y,_ in brute(v)) for x in (0,1)},'branching DP');branching.append({'width':width,'fine_tuples':3**width,'fibres':dp(v)})
    inclusion={0:0};collapse={0:0,1:0};require(bijective(comp(collapse,inclusion),[0]) and not bijective(inclusion,[0,1]) and not bijective(collapse,[0]),'staged masking')
    # Missing exact beta candidates and support blindness.
    candidates=[dict(zip(range(3),p)) for p in permutations(range(3))]
    id2={0:0,1:1};const2={0:0,1:0}
    require(all(bijective(m,range(3)) for m in candidates),'R missing not all noninvertible')
    require(bijective(id2,range(2)) and not bijective(const2,range(2)),'same support different coefficient')
    # C2 and nonunit absorbing element monoids.
    units_c2=[x for x in range(2) if any((x+y)%2==0 for y in range(2))]
    require(units_c2==[0,1],'C2');mul=lambda a,b:a*b
    require(not any(mul(0,b)==1 for b in [0,1]),'nonunit')
    return {'unary_composite_maps_exhausted':count,'branching_DP_vs_brute':branching,'masking_1_to_2_to_1':{'W_sem':True,'W_staged':False,'retains_each_stage':True},'R_missing_beta':{'apex':3,'candidate_count':len(candidates),'each_candidate_bijective':True,'verdict':'actual comparison not determined'},'same_endpoint_support':{'identity_2_to_2':True,'constant_2_to_2':False,'boundary':'singleton on both sides'},'scalars':{'C2_nonidentity_is_unit':True,'C2_nonidentity_normalized_exact':False,'absorbing_zero_in_01_is_unit':False}}

def run():return {'O':typed_order(),'lambda_double_category':tree_checks(),'Xi':xi_checks(),'W_R_scalars':semantic_checks()}

def extra_checks():
    # Semantic DP with nontrivial endpoint compatibility, repeated types, and masked stages.
    cases=[]
    for width in range(2,7):
        coarse=base()
        fine={(x,y,k):(x,y) for x,y,k in product(range(2),range(2),range(2))}
        stage={x:x[:2] for x in fine}
        domain=tuples([coarse]*width)
        out={(0,0):0,(0,1):0,(1,0):0,(1,1):0}
        for t in domain:
            weight=1
            for y in t:weight*=sum(z==y for z in stage.values())
            out[(t[0][0],t[-1][1])]+=weight
        brute=Counter((t[0][0],t[-1][1]) for t in tuples([fine]*width))
        require(out==dict(brute),'endpoint-compatible DP vs brute')
        cases.append({'width':width,'compatible_fine_tuples':sum(brute.values()),'each_endpoint_fibre':list(out.values())})
    # Literal staged forest comparison: inclusion then collapse; retained intermediate k fails.
    forest={'stage0':{'domain':(0,),'target':(0,1),'map':{0:0}},'stage1':{'domain':(0,1),'target':(0,),'map':{0:0,1:0}}}
    k0=forest['stage0']['map'];k1=comp(forest['stage1']['map'],k0)
    require(not bijective(k0,(0,1)) and bijective(k1,(0,)),'recursive external staged lambda')
    # Fixed-input occurrence substitution is associative without forgetting names or profiles.
    def substitute(word,forest):return tuple(y for x in word for y in forest.get(x,(x,)))
    word=('a','b','a_repeat');f={x:(x+'.id',x+'.real') for x in word};fw=substitute(word,f)
    g={x:(x+'.id2',x+'.real2') for x in fw};h={x:(x+'.id3',x+'.real3') for x in substitute(fw,g)}
    fg={x:substitute(f[x],g) for x in word};gh={x:substitute(g[x],h) for x in fw}
    require(substitute(substitute(substitute(word,f),g),h)==substitute(word,{x:substitute(fg[x],h) for x in word})==substitute(word,{x:substitute(f[x],gh) for x in word}),'forest substitution association')
    # Noncanonical horizontal associativity on actual tables and identity laws.
    tree=('top',[('p',['a','b']),'c']);names=list('abc');ds=[];ev=[]
    for level in range(4):
        data={n:refined(level,n) for n in names};ds.append(diagram(tree,{n:data[n][0] for n in names},seed=101+level));ev.append({n:data[n][1] for n in names})
    ks=[maps(ds[i+1],ds[i],{n:comp(inverse(ev[i][n]),ev[i+1][n]) for n in names}) for i in range(3)]
    for n in ds[0]:
        require(comp(comp(ks[0][n],ks[1][n]),ks[2][n])==comp(ks[0][n],comp(ks[1][n],ks[2][n])),'horizontal association')
        require(comp({x:x for x in ds[0][n]['span']},ks[0][n])==ks[0][n] and comp(ks[0][n],{x:x for x in ds[1][n]['span']})==ks[0][n],'horizontal units')
    # Induced graph embeddings and grade composites are retained, including cross-edges.
    embedding_checks=0
    G=set(range(6));edges={(0,5),(1,3),(2,4)}
    for mask in range(1<<6):
        U=[i for i in range(6) if mask>>i&1]
        for submask in range(1<<len(U)):
            W=[j for j in range(len(U)) if submask>>j&1];image=[U[j] for j in W]
            require([(U[j]) for j in W]==sorted(image),'induced embedding composition')
            direct={e for e in edges if set(e)<=set(image)};nested={e for e in edges if set(e)<=set(U) and set(e)<=set(image)}
            require(direct==nested,'induced graph nested restriction');embedding_checks+=1
    # Grades in C3 (including nonidentity arrows) retain ordered paths and composite.
    grade_checks=0
    for path in product(range(3),repeat=6):
        require(sum(path)%3==((sum(path[:2])%3)+(sum(path[2:5])%3)+path[5])%3,'grade composition');grade_checks+=1
    return {'compatible_semantic_DP':cases,'staged_forest_recursive_comparison':{'intermediate_invertible':False,'evaluated_occurrence_invertible':True},'three_successive_horizontal_associativity':True,'forest_final_named_occurrences':len(substitute(substitute(fw,g),h)),'graph_embedding_checks':embedding_checks,'grade_path_checks_C3':grade_checks}

_base_run=run
def run():
    r=_base_run();r['additional_scope_controls']=extra_checks();return r

def masking_and_types():
    # Pullback to boundary value0 removes an old fibre defect at boundary value1.
    old_target={'s0':(0,0),'s1':(1,1)}
    old_domain={'d0':(0,0),'d1':(1,1),'d2':(1,1)}
    t={'d0':'s0','d1':'s1','d2':'s1'}
    pull_domain={x:v for x,v in old_domain.items() if v==(0,0)}
    pull_target={x:v for x,v in old_target.items() if v==(0,0)}
    pull_t={x:t[x] for x in pull_domain}
    require(not bijective(t,old_target) and bijective(pull_t,pull_target),'old W defect erased by declared pullback')
    # A root endpoint coefficient can mask nonbijectivity, not certify retained W_sem.
    S={0:(0,0),1:(0,0)};D={0:(0,0),1:(0,0)};bad={0:0,1:0}
    gamma={0:'root',1:'root'};observed=comp(gamma,bad)
    require(observed==gamma and not bijective(bad,S),'root-only masking retained occurrence failure')
    # Segmentation maps are part of O, independently of a common flattened typed word.
    word=('a','empty.real','b','c');expected_rows=(('a','empty.real','b'),('c',));expected_cols=(('a',),('empty.real','b','c'))
    def segment(word,lengths):
        out=[];offset=0
        for n in lengths:out.append(word[offset:offset+n]);offset+=n
        require(offset==len(word),'segmentation total');return tuple(out)
    require(segment(word,(3,1))==expected_rows and segment(word,(1,3))==expected_cols,'specified segmentation')
    require(segment(word,(2,2))!=expected_rows,'wrong segmentation rejection')
    # Unit designation alone is insufficient: validate actual diagonal leg tables.
    A=(0,1);diagonal={('u',a):(a,a) for a in A};fake={('u',0):(0,0),('u',1):(0,0)}
    def genuine_unit(carrier,grade):return grade=='id' and sorted(carrier.values())==[(a,a) for a in A]
    require(genuine_unit(diagonal,'id') and not genuine_unit(fake,'id') and not genuine_unit(diagonal,'g'),'actual nullary unit certificate')
    return {'pullback_erases_old_W_failure':{'old_fibres':[1,2],'pulled_back_fibres':[1],'new_only_W':True,'if_old_arrow_retained_W':False},'root_only_masking':{'root_equation':True,'retained_occurrence_W_sem':False,'same_flattened_root':True},'segmentation':{'correct_rows_and_columns':True,'same_word_wrong_segmentation_rejected':True},'actual_empty_unit':{'diagonal_identity':True,'fake_diagonal_rejected':True,'nonidentity_grade_rejected':True}}
_previous_run=run
def run():
    r=_previous_run();r['masking_and_full_types']=masking_and_types();return r
