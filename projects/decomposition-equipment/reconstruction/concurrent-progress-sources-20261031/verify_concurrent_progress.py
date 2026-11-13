#!/usr/bin/env python3
"""Exact finite regression checks, not a proof of the general theorems. Stdlib only."""
from fractions import Fraction as F
from itertools import product, combinations
from collections import defaultdict, deque
import json, hashlib
from pathlib import Path

def frac(x): return str(x)
def run5(orders):
    w=len(orders); pc=[0]*w; own=[-1]*2; tick=0; cursor=0; seen=set(); trace=[]
    while not all(p==5 for p in pc):
        key=(tuple(pc),tuple(own),cursor)
        if key in seen: return {'completion':False,'ticks_until_repeat':tick,'trace':trace}
        seen.add(key); i=cursor; cursor=(cursor+1)%w
        if pc[i]==5: continue # companion: skipping returned modules costs no tick
        p=pc[i]; a,b=orders[i]; action=[('acquire',a),('acquire',b),('release',b),('release',a),('done',None)][p]
        tick+=1; ok=True
        if action[0]=='acquire':
            if own[action[1]]!=-1: ok=False
            else: own[action[1]]=i
        elif action[0]=='release': assert own[action[1]]==i; own[action[1]]=-1
        if ok: pc[i]+=1
        trace.append([tick,i,*action,'success' if ok else 'busy'])
    return {'completion':True,'ticks':tick,'trace':trace}

def ordered_enumeration():
    totals={'program_assignments':0,'reachable_states':0,'cursor_windows':0}
    # Programs acquire a sorted subset, one service step, then atomic release/finish.
    for r in range(1,4):
        footprints=[x for n in range(r+1) for x in combinations(range(r),n)]
        for w in range(1,4):
            for programs in product(footprints,repeat=w):
                totals['program_assignments']+=1
                def step(s,i):
                    pcs,owners=s; p=pcs[i]; fs=programs[i]
                    if p==len(fs)+2:return s,False
                    pp=list(pcs); oo=list(owners)
                    if p<len(fs):
                        if oo[fs[p]]!=-1:return s,False
                        oo[fs[p]]=i
                    elif p==len(fs)+1:
                        for rr in fs: assert oo[rr]==i; oo[rr]=-1
                    pp[i]+=1;return (tuple(pp),tuple(oo)),True
                def done(s):return all(s[0][i]==len(programs[i])+2 for i in range(w))
                initial=((0,)*w,(-1,)*r); seen={initial}; queue=deque([initial])
                while queue:
                    s=queue.popleft(); totals['reachable_states']+=1
                    edges=[step(s,i) for i in range(w)]
                    assert done(s) or any(ok for _,ok in edges)
                    for z,ok in edges:
                        if z not in seen:seen.add(z);queue.append(z)
                    if not done(s):
                        for cursor in range(w):
                            totals['cursor_windows']+=1; z=s; grants=0
                            for j in range(w):z,ok=step(z,(cursor+j)%w);grants+=ok
                            assert grants>=1
    return totals

def tail_dp(work_p=F(1,2),return_q=F(1,4)):
    # phases 0 acquire L, 1 acquire R, 2 geometric work, 3 release+return, 4 terminal.
    # A terminal visit costs one tick, unlike skipping in run5.
    state={( (0,0),(-1,-1),0):F(1)}; tails={0:F(1)}; maxstates=1
    def transitions(s):
        phases,owners,cursor=s;i=cursor;p=phases[i];nc=1-i
        if p==4 or (p<2 and owners[p]!=-1):return [( (phases,owners,nc),F(1))]
        choices=[(p+1,F(1))] if p<2 else ([(2,1-work_p),(3,work_p)] if p==2 else [(0,return_q),(4,1-return_q)])
        out=[]
        for np,pr in choices:
            pp=list(phases);oo=list(owners);pp[i]=np
            if p<2:oo[p]=i
            if p==3:
                assert oo==[i,i];oo=[-1,-1]
            out.append(((tuple(pp),tuple(oo),nc),pr))
        return out
    for tick in range(1,161):
        nxt=defaultdict(F)
        for s,mass in state.items():
            for z,p in transitions(s):
                if p and z[0]!=(4,4):nxt[z]+=mass*p
        state=dict(nxt);tails[tick]=sum(state.values(),F());maxstates=max(maxstates,len(state))
    rows=[]
    for m in range(1,5):
        for t in range(4,11):
            T=4*m*t;b=(1-work_p)**(t-3);q=return_q
            bound=2*q**m+2*sum((q**k for k in range(m)),F())*b
            actual=tails[T];assert actual<=bound
            rows.append({'m':m,'t':t,'wall_threshold':T,'tail':frac(actual),'bound_C':frac(bound),'nontrivial':bound<1})
    # Initial episodes already entered, even though no completion at tick 0.
    assert tails[1]==1 and tails[7]==1 # two episodes each need at least four grants
    return {'work_success_probability':frac(work_p),'return_probability':frac(return_q),'max_transient_states':maxstates,'horizon':160,'comparisons':len(rows),'nontrivial_comparisons':sum(x['nontrivial'] for x in rows),'initial_entered_episodes':2,'initial_completed_episodes':0,'rows':rows}

def entered_episode_dp():
    # Counters record actual entries immediately, including current unfinished episode.
    d={((0,0),(-1,-1),0,(1,1),(0,0)):F(1)}; checks=0;maxstates=1
    for tick in range(33):
        assert sum(d.values(),F())==1
        for phases,owners,cursor,entries,completed in d:
            for i in range(2):
                assert entries[i]==completed[i]+(phases[i]!=4)
                held=tuple(r for r in range(2) if owners[r]==i)
                assert held==(() if phases[i] in (0,4) else ((0,) if phases[i]==1 else (0,1)))
        for i in range(2):
            for m in range(1,5):
                observed=sum((v for k,v in d.items() if k[3][i]>m),F())
                assert observed<=F(1,4)**m;checks+=1
        if tick==32:break
        nxt=defaultdict(F)
        for (ph,own,i,en,co),mass in d.items():
            p=ph[i]
            if p==4 or (p<2 and own[p]!=-1):
                nxt[(ph,own,1-i,en,co)]+=mass;continue
            choices=[(p+1,F(1))] if p<2 else ([(2,F(1,2)),(3,F(1,2))] if p==2 else [(0,F(1,4)),(4,F(3,4))])
            for np,prob in choices:
                pp=list(ph);oo=list(own);ee=list(en);cc=list(co);pp[i]=np
                if p<2:oo[p]=i
                if p==3:
                    oo=[-1,-1];cc[i]+=1
                    if np==0:ee[i]+=1
                nxt[(tuple(pp),tuple(oo),1-i,tuple(ee),tuple(cc))]+=mass*prob
        d=dict(nxt);maxstates=max(maxstates,len(d))
    return {'horizon':32,'entry_tail_inequalities':checks,'max_states':maxstates,'statewise_entry_equals_completed_plus_active':True,'statewise_lock_cleanup':True}

# Private persistent bits with different Bernoulli emissions; busy does not read/advance them.
def emission(bit,u,o):
    if u=='busy':return F(o=='B')
    if o not in (0,1):return F(0)
    p=F(1,4) if bit==0 else F(3,4)
    return p if o==1 else 1-p

def prefix(h):
    return sum((F(1,2)*prod(emission(b,u,o) for u,o in h) for b in (0,1)),F())
def prod(xs):
    v=F(1)
    for x in xs:v*=x
    return v

def kernel(h,u,o,zero=0):
    d=prefix(h)
    return prefix(h+((u,o),))/d if d else F(o==zero)

def context(trace,adaptive):
    n=len(trace)
    i=(n%2) if not adaptive or not trace else ((trace[-1][0]+1)%2 if trace[-1][2]==1 else trace[-1][0])
    u='busy' if n%3==1 else 'grant'
    return i,u

def histories(trace):return tuple(tuple((u,o) for j,u,o in trace if j==i) for i in range(2))

def cylinders():
    normalization=0;busychecks=0
    hs={()}
    for depth in range(6):
        new=set()
        for h in hs:
            for u in ('busy','grant'):
                assert sum((kernel(h,u,o) for o in ('B',0,1)),F())==1;normalization+=1
                for o in ('B',0,1):
                    if kernel(h,u,o)>0:new.add(h+((u,o),))
            assert prefix(h+(('busy','B'),))==prefix(h);busychecks+=1
        hs=new
    impossible=(('busy',0),)
    assert prefix(impossible)==0 and kernel(impossible,'grant',0,0)==1 and kernel(impossible,'grant',1,1)==1
    counts=[];totalpaths=0;segmentchecks=0
    for adaptive in (False,True):
        direct={(bits,()):F(1,4) for bits in product((0,1),repeat=2)};rec={():F(1)}
        for n in range(8):
            pushed=defaultdict(F)
            for (bits,tr),mass in direct.items():pushed[tr]+=mass
            assert dict(pushed)==rec and sum(rec.values(),F())==1
            # Indicator rows and unit row pull back under q(bits,trace)=trace.
            assert all(sum(m for (b,tr),m in direct.items() if tr==t)==p for t,p in rec.items())
            for tr in rec:
                for cut in range(len(tr)+1):
                    first=histories(tr[:cut]);second=histories(tr[cut:])
                    assert tuple(first[i]+second[i] for i in range(2))==histories(tr)
                    segmentchecks+=1
            totalpaths+=len(direct)
            counts.append({'adaptive':adaptive,'horizon':n,'visible_prefixes':len(rec),'hidden_paths':len(direct)})
            nd=defaultdict(F);nr=defaultdict(F)
            for (bits,tr),mass in direct.items():
                i,u=context(tr,adaptive)
                for o in ('B',0,1):
                    p=emission(bits[i],u,o)
                    if p:nd[(bits,tr+((i,u,o),))]+=mass*p
            for tr,mass in rec.items():
                i,u=context(tr,adaptive);h=histories(tr)[i]
                for o in ('B',0,1):
                    p=kernel(h,u,o)
                    if p:nr[tr+((i,u,o),)]+=mass*p
            direct=dict(nd);rec=dict(nr)
    # Non-independent initial bits fail closure despite identical marginal cylinders.
    assert F(1,2)*(F(1,4)**2+F(3,4)**2)==F(5,16)!=F(1,4)
    return {'prefix_continuation_history_checks':segmentchecks,'normalized_kernels':normalization,'busy_prefix_equalities':busychecks,'path_pushforward_checks':len(counts),'hidden_paths_checked':totalpaths,'zero_prefix_variants':2,'shared_seed_negative_joint_11':'5/16 versus 1/4','rows':counts}

def private_context_closure():
    # Z is retained private context state; first supplied worker input is constant.
    # Correlated original emits Z, next visible context action also reveals Z.
    original={(0,0):F(1,2),(1,1):F(1,2)}
    reconstructed={(o,z):F(1,4) for o,z in product((0,1),repeat=2)}
    assert original!=reconstructed
    for o in (0,1):
        assert sum(v for (a,z),v in original.items() if a==o)==F(1,2)
        assert sum(v for (a,z),v in reconstructed.items() if a==o)==F(1,2)
    assert original[(0,0)]/F(1,2)==1!=F(1,2) # closure conditioned on retained Z fails
    independent={(o,z):F(1,2)*F(1,2) for o,z in product((0,1),repeat=2)}
    assert independent==reconstructed
    assert all(independent[(o,z)]/F(1,2)==F(1,2) for o,z in independent)
    return {'correlated_original_joint':{str(k):frac(v) for k,v in original.items()},
            'reconstructed_joint':{str(k):frac(v) for k,v in reconstructed.items()},
            'same_first_visible_marginal':True,'correlated_stronger_closure_fails':True,
            'independent_innovations_stronger_closure_and_joint_equality':True}

def main():
    isolated=[run5([x]) for x in ((0,1),(1,0))];assert all(x['ticks']==5 for x in isolated)
    ordered=run5([(0,1),(0,1)]);opposed=run5([(0,1),(1,0)])
    assert ordered['completion'] and not opposed['completion']
    # In ordered trace B is busy on ticks 2,4,6: no per-worker W-service promise.
    assert [x[0] for x in ordered['trace'] if x[1]==1 and x[-1]=='busy']==[2,4,6]
    flat=list('ABCABCAB'); nested=list('ACBCACBC');assert flat!=nested
    # Explicit rebracketing conjugacy for state update and unchanged flat scheduler.
    states=0
    for a,b,c in product(range(3),repeat=3):
        for i in range(3):
            l=((a,b),c);r=(a,(b,c));v=[a,b,c];v[i]+=1
            ll=((v[0],v[1]),v[2]);rr=(v[0],(v[1],v[2]))
            assert (ll[0][0],(ll[0][1],ll[1]))==rr;states+=1
    result={'status':'PASS','scope':'Exact finite regressions only; no general/infinite/CFS proof and no spawning.',
      'deterministic':{'isolated_ticks':[x['ticks'] for x in isolated],'ordered':ordered,'opposed':opposed},
      'ordered_enumeration':ordered_enumeration(),'entered_episode_DP':entered_episode_dp(),'tail_DP':tail_dp(),'bounded_service_tail_DP':tail_dp(F(1)),'controlled_cylinders':cylinders(),
      'private_context_closure':private_context_closure(),'regrouping':{'transported_scheduler_state_checks':states,'flat_trace':flat,'hierarchical_trace':nested,'different_scheduler_negative':True}}
    output=json.dumps(result,indent=2,sort_keys=True)+'\n'
    Path(__file__).with_name('verification_results.json').write_text(output)
    print(output,end='')
if __name__=='__main__':main()
