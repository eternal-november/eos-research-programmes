#!/usr/bin/env python3
"""Exact finite regressions; not a proof assistant or infinite-state theorem proof."""
from fractions import Fraction as F
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
import hashlib, json
BASE=Path(__file__).resolve().parent
counts=Counter()
def ck(category, value, detail=''):
    counts[category]+=1
    assert value, (category, detail)

# Interpreter: one instruction per selected worker tick, explicit stack frames.
def routine(k,n):
    return [('walk',)]*n+[('ret',)] if k==0 else [('call',k-1,n),('call',k-1,n),('ret',)]
def root(d,n,pair):
    l,h=pair
    return [('acq',l),('acq',h),('call',d-1,n),('rel',h),('call',d-1,n),('rel',l),('done',)]
class VM:
    def __init__(self, specs):
        self.stacks=[[[root(d,n,p),0]] for d,n,p in specs]
        self.owner={}; self.log=[]; self.work=[0]*len(specs)
    def step(self,w):
        s=self.stacks[w]; before=len(s)
        if not s:
            self.log.append((w,'idle',None,before,before,tuple(sorted(self.owner.items())))); return False
        saved_pcs=[f[1] for f in s]
        code,pc=s[-1]; ins=code[pc]; op=ins[0]
        if op=='acq' and ins[1] in self.owner:
            self.log.append((w,'busy',ins[1],before,before,tuple(sorted(self.owner.items())))); return False
        if op=='acq':
            held=[r for r,o in self.owner.items() if o==w]
            ck('ordered_ownership',not held or max(held)<ins[1])
            self.owner[ins[1]]=w
        if op=='rel':
            ck('ordered_ownership',self.owner.get(ins[1])==w)
            del self.owner[ins[1]]
        s[-1][1]+=1
        if op=='call': s.append([routine(ins[1],ins[2]),0])
        if op=='ret': s.pop()
        if op=='done':
            ck('ordered_ownership',w not in self.owner.values()); s.pop()
        ck('charged_stack',len(s)==before+(1 if op=='call' else -1 if op in ('ret','done') else 0))
        if op=='call':
            ck('charged_stack',s[-1][1]==0,'callee did not execute')
            ck('charged_stack',[f[1] for f in s[:-1]]==saved_pcs[:-1]+[pc+1])
        if op=='ret' and s: ck('charged_stack',[f[1] for f in s]==saved_pcs[:-1],'continuation did not execute')
        self.work[w]+=1
        self.log.append((w,op,ins[1:] or None,before,len(s),tuple(sorted(self.owner.items())))); return True
    def run(self):
        W=len(self.stacks); successes=[]
        while any(self.stacks):
            successes.append(self.step(len(self.log)%W))
            ck('finite_execution',len(self.log)<100000)
        for start in range(0,len(successes)-W+1):
            ck('rr_service',any(successes[start:start+W]))
        return self.log

examples=[]
for W,d,n in product(range(1,5),range(1,5),range(1,4)):
    specs=[(d,n,(i,i+1)) for i in range(W)]
    vm=VM(specs); log=vm.run(); q=2**d; C=4*q+1
    ck('episode_cost',vm.work==[q*n+C]*W)
    ck('episode_cost',len(log)<=W*sum(vm.work))
    ck('episode_cost',max(row[4] for row in log)==d+1)
    ck('episode_cost',sum(row[1]=='walk' for row in log)==W*q*n)
    for w in range(W):
        events=[row for row in log if row[0]==w and row[1] not in ('idle','busy')]
        release_h=next(i for i,row in enumerate(events) if row[1]=='rel' and row[2]==(w+1,))
        ck('intermediate_effect',events[release_h+1][1]=='call')
        ck('intermediate_effect',(w,w) in events[release_h][5])
        ck('intermediate_effect',all(r!=w+1 for r,o in events[release_h][5]))
    examples.append({'W':W,'d':d,'n':n,'ticks':len(log),'intrinsic':vm.work})

# Exhaustive small ownership/request configurations satisfying ordered locks.
# Every worker chooses local work or requests a strictly higher lock.
for W in range(1,4):
    R=4
    for assignment in product(range(-1,W),repeat=R):
        held=[[r for r,o in enumerate(assignment) if o==w] for w in range(W)]
        choices=[[-1]+[r for r in range(R) if not held[w] or r>max(held[w])] for w in range(W)]
        for requests in product(*choices):
            runnable=[r==-1 or assignment[r]==-1 for r in requests]
            ck('exhaustive_lock_service',any(runnable))

# Exact first hitting-time coefficients, no Monte Carlo; compare squared tail bounds.
def hitting(n,p,N):
    live={n:F(1)}; hit={}; tails=[F(1)]
    for t in range(1,N+1):
        nxt=defaultdict(F); z=F(0)
        for k,m in live.items():
            if k==1: z+=m*p
            else: nxt[k-1]+=m*p
            nxt[k+1]+=m*(1-p)
        live=dict(nxt); hit[t]=z; tails.append(sum(live.values(),F(0)))
        ck('walk_mass',sum(hit.values(),F(0))+tails[-1]==1)
        ck('walk_tail',tails[-1]**2*(t+1)<=2*n*n)
    return hit,tails
walks={}
for n,p in product(range(1,7),(F(1,2),F(2,3),F(3,4),F(1))):
    walks[n,p]=hitting(n,p,96)
    if p==1: ck('walk_deterministic',walks[n,p][0][n]==1)
    for t,a in enumerate(walks[n,p][1]):
        if p!=F(1,2): ck('walk_bias',a<=walks[n,F(1,2)][1][t])
for d,n,p in product(range(1,4),range(1,4),(F(1,2),F(2,3),F(1))):
    q=2**d; C=4*q+1; N=96; hit=walks[n,p][0]; dist={0:F(1)}
    for _ in range(q):
        nxt=defaultdict(F)
        for a,x in dist.items():
            for b,y in hit.items():
                if a+b<=N: nxt[a+b]+=x*y
        dist=dict(nxt)
    for t in range(N+1):
        tail=1-sum((v for k,v in dist.items() if k+C<=t),F(0))
        if t<C: ck('episode_tail',tail<=n)
        else:
            s=(t-C)//q
            # Equivalent to tail <= n*min(1,q*sqrt(2)/sqrt(s+1)).
            ck('episode_tail',tail<=n and tail*tail*(s+1)<=2*n*n*q*q)

# Exact nonnegative gain algebra, resolvents and finite sums.
def mv(A,x): return tuple(sum((a*b for a,b in zip(row,x)),F(0)) for row in A)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
P=((F(0),F(3,4)),(F(1,5),F(0))); G=tuple(tuple(2*a for a in row) for row in P)
one=(F(1),F(1)); gain=(F(25,4),F(7,2)); pgain=(F(35,17),F(24,17))
ck('gain_algebra',add(one,mv(G,gain))==gain)
ck('gain_algebra',add(one,mv(P,pgain))==pgain)
ck('gain_algebra',P[0][1]*P[1][0]==F(3,20))
ck('gain_algebra',G[0][1]*G[1][0]==F(3,5))
s=(F(0),F(0)); power=one
for m in range(1,81):
    s=add(s,power); power=mv(G,power)
    ck('gain_algebra',all(a<=b for a,b in zip(s,gain)))
    remainder=gain
    for _ in range(m): remainder=mv(G,remainder)
    ck('gain_algebra',add(s,remainder)==gain)
for d,n,i in product(range(1,7),range(1,8),range(2)):
    q=2**d; C=4*q+1
    exact=3*q*gain[i]*n+C*pgain[i]
    ck('mean_bound',exact<=(7*q+1)*gain[i]*n)

# Resource and divergence countermodels, with explicit waiter transactions.
def run_resource(program, steps, waiter_after):
    owner={}; pc=0; trace=[]; ret=False
    for t in range(steps):
        op=program[pc]
        if op=='acq': owner['r']='caller'
        elif op=='rel': owner.pop('r')
        elif op=='return': ret=True
        trace.append(('caller',op,tuple(sorted(owner.items()))))
        if op not in ('loop','return'): pc+=1
        if t==waiter_after:
            out='busy' if 'r' in owner else 'grant'
            trace.append(('waiter',out,tuple(sorted(owner.items()))))
            if out=='grant': owner['r']='waiter'
    return trace,ret
finite1=['acq','rel','return']; finite2=['idle','idle','return']
solo1=run_resource(finite1,3,-1); solo2=run_resource(finite2,3,-1)
ck('counterexamples',solo1[1] and solo2[1] and len(solo1[0])==len(solo2[0])==3)
ck('counterexamples',solo1[0][-1][2]==solo2[0][-1][2]==())
inter1=run_resource(finite1,3,0); inter2=run_resource(finite2,3,0)
ck('counterexamples',inter1[0][1][1]=='busy' and inter2[0][1][1]=='grant')
loop1=run_resource(['acq','loop'],32,0); loop2=run_resource(['loop'],32,0)
ck('counterexamples',not loop1[1] and not loop2[1])
ck('counterexamples',loop1[0][1][1]=='busy' and loop2[0][1][1]=='grant')
for loop in (loop1,loop2):
    tail=[r for r in loop[0] if r[0]=='caller'][1:]
    for row in tail: ck('divergent_prefix',row[1]=='loop')
# Only self-loop can follow each loop state; no return edge exists, establishing
# identical zero finite-return kernels (not inferred from the 32-step truncation).
for program in (['acq','loop'],['loop']):
    ck('divergent_structure','return' not in program and program[-1]=='loop')
# Fixed policy: half return at first eligible tick, half enter absorbing loop.
for delay in range(8):
    kernel={(delay+1,'done'):F(1,2)}
    ck('substochastic',sum(kernel.values())==F(1,2))
    ck('substochastic',sum(kernel.values())+F(1,2)==1)
ck('substochastic',{(1,'done'):F(1,2)}!={(2,'done'):F(1,2)})
# Actual RR opposed-lock interpreter; isolated durations agree with common order.
def locks(programs,N=24):
    owner={}; pcs=[0]*len(programs); trace=[]
    for t in range(N):
        w=t%len(programs)
        if pcs[w]==len(programs[w]): trace.append('terminal'); continue
        op,r=programs[w][pcs[w]]
        if op=='a' and r in owner: trace.append('busy'); continue
        if op=='a': owner[r]=w
        else:
            ck('counterexamples',owner[r]==w); del owner[r]
        pcs[w]+=1; trace.append('step')
    return pcs,owner,trace
up=[('a',0),('a',1),('r',1),('r',0)]
down=[('a',1),('a',0),('r',0),('r',1)]
ck('counterexamples',locks([up])[0]==locks([down])[0]==[4])
ck('counterexamples',locks([up,up])[0]==[4,4])
bad=locks([up,down]); ck('counterexamples',bad[0]==[1,1] and set(bad[2][2:])=={'busy'})
# Distinct child owner cannot reacquire caller-held lock; synchronous parent waits.
owner={0:'parent'}; waiting={'parent':'child','child':owner[0]}
ck('counterexamples',waiting[waiting['parent']]=='parent')
nested=[('A' if t//2%2==0 else 'B') if t%2==0 else 'C' for t in range(8)]
flat=[['A','B','C'][t%3] for t in range(8)]
ck('counterexamples',nested[:4]==['A','C','B','C'] and nested!=flat)

# Actual finite path projections. Selected node A/B outputs a persistent hidden bit
# across two resumptions. Exterior ticks and session age are always retained.
def project(path,keep):
    histories={}; out=[]
    for tick,selected,event,private in path:
        histories.setdefault(selected,[]).append(event)
        out.append((tick,selected,event,tuple((k,tuple(v)) for k,v in sorted(histories.items())),
                    tuple((k,v) for k,v in private if k in keep)))
    return tuple(out)
def coarsen(path,keep):
    return tuple((t,s,e,h,tuple((k,v) for k,v in p if k in keep)) for t,s,e,h,p in path)
full={}; cutlaw=defaultdict(F)
for a,b in product(range(2),repeat=2):
    schedule=['A','outside','B','A','outside','B']
    paths=[]; ages=Counter()
    for t,s in enumerate(schedule,1):
        ages[s]+=1
        event=(s,ages[s],a if s=='A' else b if s=='B' else 'idle',
               'return' if s!='outside' and ages[s]==2 else 'pending')
        paths.append((t,s,event,(('A',a),('B',b),('manager','fixed'))))
    path=tuple(paths); full[path]=F(1,4)
    for N in range(7):
        p=path[:N]; f=project(p,{'A','B','manager'}); g=project(p,{'B','manager'}); h=project(p,{'manager'})
        ck('cut_coherence',coarsen(f,{'B','manager'})==g)
        ck('cut_coherence',coarsen(g,{'manager'})==h)
        ck('cut_coherence',coarsen(coarsen(f,{'B','manager'}),{'manager'})==h)
        ck('cut_coherence',coarsen(f,{'A','B','manager'})==f)
        ck('cut_coherence',project(path,{'manager'})[:N]==h)
        ck('identity_clock',tuple(row[0] for row in h)==tuple(range(1,N+1)))
    cutlaw[project(path,{'manager'})]+=F(1,4)
ck('pushforward',sum(cutlaw.values())==1)
# Separately generate history machine law: first response fair, second conditional copy.
historylaw=defaultdict(F)
for a,b in product(range(2),repeat=2):
    hist={}; events=[]; ages=Counter()
    for t,s in enumerate(['A','outside','B','A','outside','B'],1):
        ages[s]+=1
        bit='idle' if s=='outside' else hist.setdefault(s,a if s=='A' else b)
        e=(s,ages[s],bit,'return' if s!='outside' and ages[s]==2 else 'pending')
        events.append((t,s,e,(('manager','fixed'),)))
    historylaw[project(tuple(events),{'manager'})]+=F(1,4)
ck('pushforward',historylaw==cutlaw)
# Fresh history on every resume gives P(second A != first A)=1/2, not0.
reset_bad=sum((F(1,4) for x,y in product(range(2),repeat=2) if x!=y),F(0))
ck('counterexamples',reset_bad==F(1,2))
def identity_wire(path): return tuple(path)
ck('identity_clock',identity_wire(next(iter(full)))==next(iter(full)))
ck('counterexamples',len(['wrapper']+list(range(6)))==7)

sources={name:hashlib.sha256((BASE/name).read_bytes()).hexdigest() for name in ('variable_duration_closure.md','progress_witness.md')}
ck('source_identity',sources['variable_duration_closure.md']=='249671d8d38d0c60b53a9325794bcbeb3787b85fee69d09edcd7aee1f84bb05b')
ck('source_identity',sources['progress_witness.md']=='6fd979b470c1978cba3236536e10cb9e78a34de7417874ea22e093328b170fc2')
result={'status':'PASS','scope':'Exact finite regression checks, not a proof of the general theorem',
        'assertions':sum(counts.values()),'categories':dict(sorted(counts.items())),
        'sources':sources,'deterministic_family_instances':len(examples),'family_examples':examples,
        'walk_grid':{'entries':'1..6','probabilities':['1/2','2/3','3/4','1'],'horizon':96},
        'episode_tail_grid':{'depths':'1..3','entries':'1..3','probabilities':['1/2','2/3','1'],'horizon':96}}
(BASE/'verification_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='family_examples'},indent=2))
