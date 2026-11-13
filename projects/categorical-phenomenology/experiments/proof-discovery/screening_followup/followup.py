#!/usr/bin/env python3
"""Fresh fixed-family test of cheap finite screening, with matched baselines."""
import collections,hashlib,itertools,json,random,sys,time
from pathlib import Path
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
import experiment as e
import kernel

# Grammar and orientation are identical to the original enumerator. Only the
# number of finite screening assignments changes, before proof checking.
def candidates(cost,screen):
    levels={1:[e.N,e.X,e.Y,e.Z]}
    for n in range(2,6):
        ts=[]
        for a in levels[n-1]:cost.add('grammar');ts.append(e.R(a))
        for i in range(1,n-1):
            for a in levels[i]:
                for b in levels[n-1-i]:cost.add('grammar');ts.append(e.A(a,b))
        levels[n]=ts
    vs=[()]+[(x,) for x in (0,1)]+list(itertools.product((0,1),repeat=2))
    assignments=[dict(zip('XYZ',v3)) for v3 in itertools.product(vs,repeat=3)]
    if screen==8:
        assignments=random.Random(20261103).sample(assignments,8)
        cost.add('screen_sampling',len(assignments))
    groups=collections.defaultdict(list)
    for t in itertools.chain.from_iterable(levels.values()):
        sig=tuple(e.eval_term(t,a,cost) for a in assignments)
        cost.add('signature_hash',len(sig));groups[sig].append(t)
    eqs=set()
    for g in groups.values():
        for a,b in itertools.combinations(g,2):
            cost.add('candidate_pair')
            if e.vars_(a)!=e.vars_(b):continue
            eq=e.orient((a,b),cost)
            if eq:eqs.add(e.canonical(eq,cost))
    return sorted(eqs,key=lambda eq:(sum(map(e.size,eq)),repr(eq)))


def random_term(n,rng):
    if n==1:return rng.choice([e.X,e.Y,e.Z,e.N])
    f=rng.choice(['rev'] if n==2 else ['rev','app','cons'])
    if f=='rev':return e.R(random_term(n-1,rng))
    if f=='cons':return e.C(rng.choice([e.a,e.b]),random_term(n-2,rng))
    left=rng.randrange(1,n-1)
    return e.A(random_term(left,rng),random_term(n-1-left,rng))


def word(t):
    if t[0]=='v':return [('var',t[1],False)]
    if t[0]=='nil':return []
    if t[0]=='cons':return [('element',t[1][1],False)]+word(t[2])
    if t[0]=='app':return word(t[1])+word(t[2])
    if t[0]=='rev':return [(kind,name,(not flip) if kind=='var' else False) for kind,name,flip in word(t[1])[::-1]]
    raise ValueError(t)


def normal_form(t):
    out=e.N
    for kind,name,flip in word(t)[::-1]:
        if kind=='element':out=e.C(e.E(name),out)
        else:
            atom=e.R(e.V(name)) if flip else e.V(name)
            out=atom if out==e.N else e.A(atom,out)
    return out


def alter_one_variable(t):
    if t[0]=='v':return e.V('W'),True
    if t[0] in ('nil','e'):return t,False
    args=list(t[1:])
    for i,x in enumerate(args):
        y,done=alter_one_variable(x)
        if done:args[i]=y;return (t[0],*args),True
    return t,False


def semantic_eval(t,env):
    if t[0]=='v':return env[t[1]]
    if t[0]=='nil':return ()
    if t[0]=='cons':return (env[t[1][1]],)+semantic_eval(t[2],env)
    if t[0]=='app':return semantic_eval(t[1],env)+semantic_eval(t[2],env)
    if t[0]=='rev':return semantic_eval(t[1],env)[::-1]
    raise ValueError(t)


def freeze_workload():
    rng=random.Random(20261104);cases=[];seen=set()
    while len(cases)<100:
        lhs=random_term(rng.randint(9,23),rng)
        if not any(t[0]=='rev' for t in e.subterms(lhs)):continue
        if len({t for t in e.vars_(lhs) if t[0]=='v'})<2:continue
        rhs=normal_form(lhs)
        if lhs==rhs or (lhs,rhs) in seen:continue
        seen.add((lhs,rhs));cases.append({'id':f'positive_{len(cases):03d}','equation':(lhs,rhs),'expected':True})
    for i,c in enumerate(cases[:20]):
        lhs,rhs=c['equation'];bad,done=alter_one_variable(rhs);assert done
        valuation={'X':(),'Y':(),'Z':(),'W':(0,),'a':0,'b':0}
        assert semantic_eval(lhs,valuation)!=semantic_eval(bad,valuation)
        cases.append({'id':f'negative_{i:03d}','equation':(lhs,bad),'expected':False,'counterexample':valuation})
    rng.shuffle(cases)
    (P/'workload.json').write_text(json.dumps(cases,indent=2)+'\n')
    with (P/'FROZEN_SHA256.txt').open('w') as f:
        for name in ['PROTOCOL.json','followup.py','workload.json']:
            f.write(hashlib.sha256((P/name).read_bytes()).hexdigest()+'  '+name+'\n')
    print('Frozen 100 positives and 20 independently falsified controls; no outcomes have been measured.')


def run(mode,screen,cap):
    cost=e.Cost(cap);start=time.perf_counter();cpu=time.process_time();library=[];proofs=[];results=[];history=[];status='complete'
    original=e.generate_candidates;e.generate_candidates=lambda c:candidates(c,screen)
    try:
        library,trainproof,history,attempts=e.discover(mode,cost,full=True)
        acquisition=cost.total
        # The held-out file is not even opened until discovery is finished.
        cases=json.loads((P/'workload.json').read_text())
        for item in cases:
            before=cost.total;eq=tuple(kernel.freeze(t) for t in item['equation'])
            cert,_=e.prove(eq,library,cost)
            if cert:
                e.verify(eq,cert,library,cost)
                proofs.append({'name':item['id'],'equation':eq,'certificate':cert})
                if not item['expected']:raise AssertionError('FALSE CONTROL ACCEPTED')
            results.append({'id':item['id'],'expected':item['expected'],'proved':bool(cert),'cost':cost.total-before})
    except e.OutOfBudget:status='budget_exhausted';acquisition=locals().get('acquisition',cost.total)
    finally:e.generate_candidates=original
    elapsed=time.perf_counter()-start;cpu=time.process_time()-cpu
    bundle={'library':library,'proofs':proofs};kernel.check_bundle(bundle)
    return {'mode':mode,'screen_size':screen,'cap':cap,'status':status,'cost':cost.state(),'acquisition':acquisition,'cpu_seconds':cpu,'wall_seconds':elapsed,'positive_solved':sum(r['proved'] and r['expected'] for r in results),'negative_rejected':sum(not r['proved'] and not r['expected'] for r in results),'false_acceptances':sum(r['proved'] and not r['expected'] for r in results),'history':history,'results':results,'bundle':bundle}


def main():
    if '--freeze' in sys.argv:freeze_workload();return
    if not (P/'FROZEN_SHA256.txt').exists():raise RuntimeError('Freeze before running')
    for line in (P/'FROZEN_SHA256.txt').read_text().splitlines():
        h,name=line.split();assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h,'Frozen file changed'
    dest=P/'results';dest.mkdir(exist_ok=True);summary=[]
    for cap in [100000,250000,1000000]:
        for screen in [343,8]:
            for mode in ['generic','guided']:
                r=run(mode,screen,cap)
                (dest/f'{mode}_screen{screen}_cap{cap}.json').write_text(json.dumps(r,indent=2)+'\n')
                s={k:v for k,v in r.items() if k not in ('bundle','results','history')};summary.append(s);print(json.dumps(s),flush=True)
    (dest/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')

if __name__=='__main__':main()
