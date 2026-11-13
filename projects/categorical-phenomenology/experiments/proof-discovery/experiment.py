#!/usr/bin/env python3
"""Dependency-free checked lemma discovery diagnostic. See README.md."""
import argparse,collections,hashlib,itertools,json,random,time
from pathlib import Path
import kernel

ROOT=Path(__file__).resolve().parent
V=lambda name:('v',name)
E=lambda name:('e',name)
N=('nil',)
A=lambda a,b:('app',a,b)
R=lambda a:('rev',a)
C=lambda a,b:('cons',a,b)
X,Y,Z=map(V,'XYZ')
a,b=map(E,'ab')

class OutOfBudget(Exception): pass
class Cost:
    def __init__(self,limit=10**12,cpu_limit=None):
        self.parts=collections.Counter(); self.limit=limit; self.total=0
        self.cpu_limit=cpu_limit; self.cpu_start=time.process_time(); self.next_check=0
    def add(self,part,n=1):
        if self.total+n>self.limit: raise OutOfBudget()
        if self.cpu_limit is not None and self.total>=self.next_check:
            self.next_check=self.total+128
            if time.process_time()-self.cpu_start>=self.cpu_limit: raise OutOfBudget()
        self.parts[part]+=n; self.total+=n
    def state(self): return {'total':self.total,'components':dict(sorted(self.parts.items()))}

# Deliberately separate implementations from the checker.
def size(t): return 1+sum(size(x) for x in t[1:] if isinstance(x,tuple)) if t[0] not in ('v','e') else 1

def vars_(t):
    if t[0] in ('v','e'): return {t}
    return set().union(*(vars_(a) for a in t[1:])) if len(t)>1 else set()

def subst(t,env,cost):
    cost.add('search_substitute')
    if t[0] in ('v','e'): return env.get(t,t)
    return (t[0],*(subst(a,env,cost) for a in t[1:]))

def mtch(p,t,env,fixed,cost):
    cost.add('search_match')
    if p[0] in ('v','e'):
        if p in fixed: return p==t
        if (p[0]=='e')!=(t[0]=='e'): return False
        if p in env: return env[p]==t
        env[p]=t; return True
    return p[0]==t[0] and len(p)==len(t) and all(mtch(x,y,env,fixed,cost) for x,y in zip(p[1:],t[1:]))

PREC={'nil':0,'cons':1,'app':2,'rev':3}
def lpo(s,t,cost):
    cost.add('ordering')
    if s==t or s[0] in ('v','e'): return False
    if t[0] in ('v','e'): return t in vars_(s)
    if any(x==t or lpo(x,t,cost) for x in s[1:]): return True
    if not all(lpo(s,y,cost) for y in t[1:]): return False
    if PREC[s[0]]>PREC[t[0]]: return True
    if s[0]!=t[0]: return False
    for x,y in zip(s[1:],t[1:]):
        if x!=y: return lpo(x,y,cost)
    return False


def fmt(t):
    f=t[0]
    if f in ('v','e'):return t[1]
    if f=='nil': return '[]'
    if f=='app':return '('+fmt(t[1])+' ++ '+fmt(t[2])+')'
    if f=='rev':return 'rev('+fmt(t[1])+')'
    return 'cons('+fmt(t[1])+','+fmt(t[2])+')'


def orient(eq,cost):
    if lpo(eq[0],eq[1],cost): return eq
    if lpo(eq[1],eq[0],cost): return eq[::-1]
    return None


def normalize(t,rules,cost,max_steps=1000):
    # Innermost rewriting; rules indexed by head symbol. Each RHS recursively
    # normalizes, so learned and primitive rules receive the same traversal.
    index=collections.defaultdict(list)
    for name,lhs,rhs,fixed in rules:
        cost.add('rule_index'); index[lhs[0]].append((name,lhs,rhs,fixed))
    trace=[]
    def norm(u,path):
        cost.add('search_visit')
        if u[0] in ('v','e'): return u
        u=(u[0],*(norm(x,path+(i,)) for i,x in enumerate(u[1:],1)))
        for name,lhs,rhs,fixed in index[u[0]]:
            env={}
            if mtch(lhs,u,env,fixed,cost):
                v=subst(rhs,env,cost)
                if v==u: continue
                if len(trace)>=max_steps: raise RuntimeError('Rewrite step limit')
                trace.append({'rule':name,'path':list(path)})
                return norm(v,path)
        return u
    result=norm(t,())
    return result,trace


def rules_for(library,cost,ih=None):
    rules=[(name,*eq,set()) for name,eq in kernel.AXIOMS.items()]
    for ent in library: rules.append((ent['name'],*ent['equation'],set()))
    if ih:
        oriented=orient(ih[0],cost)
        if oriented and oriented==ih[0]: rules.insert(0,('IH',*oriented,{ih[1]}))
        elif oriented:
            # checker supports reverse rewrite explicitly, but simpler search
            # skips reverse-oriented induction hypotheses in this diagnostic.
            pass
    return rules


def prove(eq,library,cost,collect=False):
    cost.add('proof_attempt')
    frontiers=[]
    def solve(left,right,rules):
        nl,tl=normalize(left,rules,cost); nr,tr=normalize(right,rules,cost)
        if nl==nr:return {'left':tl,'right':tr}
        if collect:frontiers.extend([nl,nr])
        return None
    rules=rules_for(library,cost)
    cert=solve(*eq,rules)
    if cert:return dict(mode='rewrite',**cert),frontiers
    names={v[1] for t in eq for v in vars_(t)}
    tailname='_t'
    while tailname in names:tailname+='t'
    headname='_a'
    while headname in names:headname+='a'
    tail=V(tailname);head=E(headname)
    for var in sorted(set.union(*(vars_(t) for t in eq))):
        if var[0]!='v':continue
        base=tuple(subst(t,{var:N},cost) for t in eq)
        bc=solve(*base,rules)
        if bc is None:continue
        ih=tuple(subst(t,{var:tail},cost) for t in eq)
        step=tuple(subst(t,{var:C(head,tail)},cost) for t in eq)
        sc=solve(*step,rules_for(library,cost,(ih,tail)))
        if sc is not None:
            return {'mode':'induction','variable':var[1],'tail':tailname,'head':headname,'base':bc,'step':sc},frontiers
    return None,frontiers


def verify(eq,cert,library,cost):
    meter=kernel.Meter()
    # Check completes atomically, then its full independently counted work is
    # charged; a result exceeding budget is not retained or counted successful.
    kernel.check_equation(eq,cert,{x['name']:x['equation'] for x in library},meter)
    cost.add('kernel',meter.ticks)


def eval_term(t,env,cost):
    cost.add('finite_eval')
    f=t[0]
    if f=='v':return env[t[1]]
    if f=='nil':return ()
    if f=='rev':return eval_term(t[1],env,cost)[::-1]
    if f=='app':return eval_term(t[1],env,cost)+eval_term(t[2],env,cost)
    raise ValueError(f)


def canonical(eq,cost):
    env={}; names=iter('XYZUVW')
    def f(t):
        cost.add('candidate_canonicalize')
        if t[0]=='v':
            if t not in env:env[t]=V(next(names))
            return env[t]
        if t[0]=='nil':return t
        return (t[0],*(f(x) for x in t[1:]))
    return tuple(f(t) for t in eq)


def generate_candidates(cost):
    levels={1:[N,X,Y,Z]}
    for n in range(2,6):
        terms=[]
        for a in levels[n-1]: cost.add('grammar'); terms.append(R(a))
        for i in range(1,n-1):
            for a in levels[i]:
                for b in levels[n-1-i]:cost.add('grammar'); terms.append(A(a,b))
        levels[n]=terms
    values=[()]+[(x,) for x in (0,1)]+list(itertools.product((0,1),repeat=2))
    assignments=[dict(zip('XYZ',values3)) for values3 in itertools.product(values,repeat=3)]
    groups=collections.defaultdict(list)
    for t in itertools.chain.from_iterable(levels.values()):
        sig=tuple(eval_term(t,env,cost) for env in assignments)
        cost.add('signature_hash',len(sig)); groups[sig].append(t)
    equations=set()
    for group in groups.values():
        for a,b in itertools.combinations(group,2):
            cost.add('candidate_pair')
            if vars_(a)!=vars_(b):continue
            eq=orient((a,b),cost)
            if eq:equations.add(canonical(eq,cost))
    return sorted(equations,key=lambda eq:(sum(map(size,eq)),repr(eq)))


def subterms(t):
    yield t
    if t[0] not in ('v','e'):
        for x in t[1:]:yield from subterms(x)


def ranked(candidates,mode,frontiers,cost,seed=11):
    if mode=='generic':return candidates
    if mode=='random':
        candidates=list(candidates);random.Random(seed).shuffle(candidates)
        cost.add('ranking',len(candidates));return candidates
    scored=[]
    for eq in candidates:
        score=0
        for t in frontiers:
            for sub in subterms(t):
                cost.add('ranking')
                if mtch(eq[0],sub,{},set(),cost):score+=1
        scored.append((-score,sum(map(size,eq)),repr(eq),eq))
    return [x[-1] for x in sorted(scored)]

TRAIN=(R(R(X)),X)

def fixed_cases():
    positive=[
      ('rev_app',R(A(X,Y)),A(R(Y),R(X))),
      ('rev_revapp_left',R(A(R(X),Y)),A(R(Y),X)),
      ('rev_revapp_right',R(A(X,R(Y))),A(Y,R(X))),
      ('rev_three_left',R(A(A(X,Y),Z)),A(R(Z),A(R(Y),R(X)))),
      ('rev_three_right',R(A(X,A(Y,Z))),A(R(Z),A(R(Y),R(X)))),
      ('rev_nested',R(A(R(A(X,Y)),Z)),A(R(Z),A(X,Y))),
      ('rev_nested_other',R(A(X,R(A(Y,Z)))),A(A(Y,Z),R(X))),
      ('rev_both',R(A(R(X),R(Y))),A(Y,X)),
      ('rev_double_pair',R(R(A(X,Y))),A(X,Y)),
      ('rev_four_repeated',R(A(A(X,Y),A(Z,X))),A(R(X),A(R(Z),A(R(Y),R(X))))),
      ('rev_cons_append',R(A(C(a,X),Y)),A(R(Y),A(R(X),C(a,N)))),
      ('nested_involution',R(A(R(A(R(X),Y)),Z)),A(R(Z),A(R(X),Y))),
    ]
    shifted=[
      ('app_nil_def',A(N,X),X),
      ('app_cons_def',A(C(a,X),Y),C(a,A(X,Y))),
      ('app_two_cons_def',A(C(a,C(b,X)),Y),C(a,C(b,A(X,Y)))),
      ('app_nil_nested',A(N,A(N,X)),X),
      ('app_cons_nil_def',A(C(a,N),Y),C(a,Y)),
      ('rev_cons_nil_def',R(C(a,N)),C(a,N)),
      ('rev_two_cons_def',R(C(a,C(b,N))),C(b,C(a,N))),
      ('rev_nil_def',R(N),N),
    ]
    return [(name,(l,r),'transfer') for name,l,r in positive]+[(name,(l,r),'definition_control') for name,l,r in shifted]


def discover(mode,cost,seed=11,target=TRAIN,full=False):
    library=[]; attempts=[]; history=[]
    cert,frontiers=prove(target,library,cost,True)
    if cert:
        verify(target,cert,library,cost)
        return library,cert,history,attempts
    targetproof=None
    candidates=generate_candidates(cost)
    history.append({'event':'candidates','count':len(candidates),'cost':cost.total})
    ordered=ranked(candidates,mode,frontiers,cost,seed)
    remaining=list(ordered)
    while remaining:
        progress=False; retry=[]
        for eq in remaining:
            before=cost.total
            # If normalizes under existing rules, it adds no new library entry.
            direct_rules=rules_for(library,cost)
            nl,_=normalize(eq[0],direct_rules,cost); nr,_=normalize(eq[1],direct_rules,cost)
            if nl==nr:continue
            proof,new_frontier=prove(eq,library,cost,True)
            attempts.append({'equation':[fmt(t) for t in eq],'proved':proof is not None,'cost':cost.total-before})
            if proof is not None:
                verify(eq,proof,library,cost)
                entry={'name':f'lemma_{len(library):03d}','equation':eq,'certificate':proof}
                library.append(entry);progress=True
                history.append({'event':'lemma','name':entry['name'],'equation':[fmt(t) for t in eq],'cost':cost.total})
                candidateproof,stalls=prove(target,library,cost,True)
                if candidateproof and targetproof is None:
                    verify(target,candidateproof,library,cost)
                    targetproof=candidateproof
                    history.append({'event':'target_solved','cost':cost.total})
                    if not full:return library,targetproof,history,attempts
                    library.append({'name':'training_cached','equation':target,'certificate':targetproof})
                frontiers+=stalls
            else:retry.append(eq)
        if not progress:break
        remaining=ranked(retry,mode,frontiers,cost,seed)
    return library,targetproof,history,attempts


def run_method(name,budget,seed=11,cpu_limit=None):
    cost=Cost(budget,cpu_limit);start=time.perf_counter();cpu_start=time.process_time();library=[];proofs=[];history=[];attempts=[];cold_bundles=[]
    results=[];trainproof=None;status='complete'
    try:
        if name in ('generic','guided','random','full_completion','guided_full_completion'):
            library,trainproof,history,attempts=discover('generic' if name=='full_completion' else ('guided' if name=='guided_full_completion' else name),cost,seed,full=name in ('full_completion','guided_full_completion'))
            if trainproof and not any(e['name']=='training_cached' for e in library):
                library.append({'name':'training_cached','equation':TRAIN,'certificate':trainproof})
        elif name=='training_cache':
            # Acquisition is charged using generic completion, then discard
            # intermediate library. Revalidate the training theorem using a
            # private dependency bundle, not as a new unjustified axiom.
            acquisition,trainproof,history,attempts=discover('generic',cost)
            library=acquisition
        elif name=='definitions':
            trainproof,_=prove(TRAIN,[],cost)
        elif name=='oracle':
            # Deliberately supplied standard normalizing equations, separately
            # proved and checked; human selection cost is NOT captured.
            for eq in [(A(X,N),X),(A(A(X,Y),Z),A(X,A(Y,Z))),(R(A(X,Y)),A(R(Y),R(X))),(R(R(X)),X)]:
                p,_=prove(eq,library,cost)
                if p is None:raise AssertionError('Oracle certification failed')
                verify(eq,p,library,cost)
                library.append({'name':f'lemma_{len(library):03d}','equation':eq,'certificate':p})
            trainproof,_=prove(TRAIN,library,cost)
        elif name=='cold':
            _,trainproof,history,attempts=discover('generic',cost)
        else:raise ValueError(name)
        training_cost=cost.total
        active=library
        if name=='training_cache' and trainproof:
            active=[{'name':'training_cached','equation':TRAIN,'certificate':trainproof}]
        for case,(lhs,rhs),split in fixed_cases():
            before=cost.total
            if name=='cold':
                active,targetproof,h,a=discover('generic',cost,target=(lhs,rhs))
                # Private discovery is rebuilt for each actual target.
            p,_=prove((lhs,rhs),active,cost)
            if p:
                checklib=active
                if name=='training_cache':
                    # training_cached has already been proved from the primitive
                    # theory via acquisition; supply it to checker as checked.
                    checklib=active
                verify((lhs,rhs),p,checklib,cost)
                proofs.append({'name':case,'equation':(lhs,rhs),'certificate':p})
                if name=='cold':cold_bundles.append({'library':active,'proofs':[proofs[-1]]})
            exact_overlap=any(ent['equation']==(lhs,rhs) for ent in active)
            results.append({'name':case,'split':split,'proved':p is not None,'cost':cost.total-before,'exact_library_overlap':exact_overlap})
    except OutOfBudget:
        status='budget_exhausted';training_cost=locals().get('training_cost',cost.total)
    elapsed=time.perf_counter()-start;cpu_seconds=time.process_time()-cpu_start
    # Full independently checkable bundles for retained and direct baselines.
    bundle=None
    if name not in ('cold','training_cache'):
        bundle={'library':library,'proofs':proofs}
        kernel.check_bundle(bundle)
    elif name=='training_cache' and trainproof:
        bundle={'library':library+[{'name':'training_cached','equation':TRAIN,'certificate':trainproof}],'proofs':proofs}
        kernel.check_bundle(bundle)
    return {'method':name,'seed':seed,'budget':budget,'status':status,'cost':cost.state(),'training_cost':training_cost,
            'elapsed_seconds':elapsed,'cpu_seconds':cpu_seconds,'cpu_limit':cpu_limit,'training_proved':trainproof is not None,'library_size':len(library),
            'results':results,'history':history,'candidate_attempts':attempts,'bundle':bundle,'cold_bundles':cold_bundles}


def summarize(run):
    out={k:v for k,v in run.items() if k not in ('bundle','candidate_attempts','history','cold_bundles')}
    out['transfer_solved']=sum(x['proved'] for x in run['results'] if x['split']=='transfer')
    out['compositional_transfer_solved']=sum(x['proved'] for x in run['results'] if x['split']=='transfer' and x['name'] in {n for n,e,s in fixed_cases() if s=='transfer' and max(map(size,e))>5})
    out['definition_control_solved']=sum(x['proved'] for x in run['results'] if x['split']=='definition_control')
    return out


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--method',choices=['generic','guided','random','training_cache','definitions','oracle','cold','full_completion','guided_full_completion','all'],default='all');parser.add_argument('--budget',type=int,default=10000000);parser.add_argument('--cpu-limit',type=float);parser.add_argument('--seed',type=int,default=11)
    args=parser.parse_args();outdir=ROOT/'results';outdir.mkdir(exist_ok=True)
    methods=['definitions','training_cache','generic','guided','full_completion','guided_full_completion','cold','oracle'] if args.method=='all' else [args.method]
    summaries=[]
    for method in methods:
        run=run_method(method,args.budget,args.seed,args.cpu_limit)
        suffix=f'{args.budget}' + (f'_cpu{args.cpu_limit}' if args.cpu_limit is not None else '') + (f'_seed{args.seed}' if method=='random' else '')
        with (outdir/f'{method}_{suffix}.json').open('w') as f:json.dump(run,f,indent=2)
        if run['bundle'] is not None:
            with (outdir/f'{method}_{suffix}_proofs.json').open('w') as f:json.dump(run['bundle'],f,indent=2)
        row=summarize(run);summaries.append(row);print(json.dumps(row,sort_keys=True),flush=True)
    with (outdir/f'summary_{args.method}_{suffix}.json').open('w') as f:json.dump(summaries,f,indent=2)

if __name__=='__main__':main()
