#!/usr/bin/env python3
"""Exact finite checks for the raw-interface docking family. Python standard library."""
import itertools, json
from pathlib import Path
B=(0,1); Q=('ready','goal','crash'); A=('wait','dock0','dock1')
def bits(n): return tuple(itertools.product(B, repeat=n))
def par(y): return sum(y)%2
def step(q,y,a):
    if q!='ready' or a=='wait': return q
    return 'goal' if int(a[-1])==par(y) else 'crash'
def proj(y,H): return tuple(y[i] for i in H)
def whole(n):
    return {(q,y,a,step(q,y,a),e) for q in Q for y in bits(n) for a in A for e in bits(n)}
def image(W,H): return {(q,proj(y,H),a,q1,proj(e,H)) for q,y,a,q1,e in W}
def loose_robot():
    return {(q,a,q1) for q in Q for a in A for q1 in (('goal','crash') if q=='ready' and a!='wait' else (q,))}
def marginal_product(h):
    return {(q,y,a,q1,e) for q,a,q1 in loose_robot() for y in bits(h) for e in bits(h)}
def subsets(I):
    I=tuple(I)
    return [tuple(I[j] for j in range(len(I)) if mask>>j&1) for mask in range(1<<len(I))]
def exact_raw_cut(n,J,Bd):
    """Minimal candidate T obtained by projecting actual transitions. Any exact T must contain it.
    Return whether independently recombining with context adds no event and loses none.
    Reset coordinates remain actual local event records, not discarded nondeterminism.
    """
    K=tuple(i for i in range(n) if i not in J)
    W=whole(n)
    T={(q,proj(y,J),a,proj(y,Bd),q1,proj(e,J)) for q,y,a,q1,e in W}
    C={(proj(y,K),a,proj(y,Bd),proj(e,K)) for _,y,a,_,e in W}
    # Reconstruct product events indexed by their literal actual local reset records.
    bykey={}
    for yK,a,b,eK in C: bykey.setdefault((a,b),[]).append((yK,eK))
    rebuilt=set()
    for q,yJ,a,b,q1,eJ in T:
        for yK,eK in bykey[(a,b)]:
            y=[None]*n; e=[None]*n
            for i,v,w in zip(J,yJ,eJ): y[i]=v; e[i]=w
            for i,v,w in zip(K,yK,eK): y[i]=v; e[i]=w
            rebuilt.add((q,tuple(y),a,q1,tuple(e)))
    return rebuilt==W,len(rebuilt-W),len(T),len(C)
def immediate_uniform_safe_action(n,observed):
    # Safe progress requires a dock action at some point. In this reset family every
    # observation fibre can recur with every hidden mode, so this is also exact for
    # arbitrary-memory sure-safe eventual docking, not a generic memoryless claim.
    obs={}
    for y in bits(n): obs.setdefault(proj(y,observed),[]).append(y)
    for ys in obs.values():
        if not any(all(step('ready',y,a)=='goal' for y in ys) for a in ('dock0','dock1')):
            return False
    return True

def main():
    out={'scope':'n=2..4 exact event enumeration; n=2..8 budget and observation enumeration','instances':[]}
    for n in range(2,5):
        W=whole(n); I=tuple(range(n)); marginal_checks=0
        for H in subsets(I):
            if len(H)==n: continue
            assert image(W,H)==marginal_product(len(H))
            marginal_checks+=1
        joint=marginal_product(n)
        assert W<joint
        assert len(joint-W)==2*4**n
        # Every full join event projects into every single-omission image.
        for v in joint:
            q,y,a,q1,e=v
            assert all((q,proj(y,tuple(i for i in I if i!=j)),a,q1,proj(e,tuple(i for i in I if i!=j)))
                       in image(W,tuple(i for i in I if i!=j)) for j in I)
        cut_checks=0; exact_cuts=0; failures=0
        for J in subsets(range(n-1)): # last mode is protected external infrastructure
            K=tuple(i for i in I if i not in J)
            for Bd in subsets(K):
                exact,extras,tcount,ccount=exact_raw_cut(n,J,Bd)
                assert exact==(Bd==K)
                assert exact==(extras==0)
                cut_checks+=1; exact_cuts+=exact; failures+=not exact
        out['instances'].append({'n':n,'whole_events':len(W),'locally_compatible_join_events':len(joint),
            'spurious_join_events':len(joint-W),'proper_marginal_checks':marginal_checks,
            'raw_cut_checks':cut_checks,'exact_raw_cuts':exact_cuts,'failed_raw_cuts':failures})
    budgets=0; observations=0
    for n in range(2,9):
        for O in subsets(range(n)):
            assert immediate_uniform_safe_action(n,O)==(len(O)==n)
            observations+=1
        for k in range(n+1):
            for l in range(n+1):
                witnesses=[]
                for J in subsets(range(n-1)):
                    K=tuple(i for i in range(n) if i not in J)
                    if len(K)<=k and len(J)<=l: witnesses.append(J)
                assert bool(witnesses)==(k>=1 and k+l>=n)
                budgets+=1
    out['observation_subsets_checked']=observations
    out['budget_pairs_checked']=budgets
    out['three_mode_minimal_example']={'mode_indices':'zero-based in this JSON; note uses one-based mathematical subscripts',
        'k':2,'l':0,'persistent_cuts':[[0],[1],[0,1]],'controlled_cuts':[],
        'repair':{'k':2,'l':1,'choose_J':[0],'boundary_modes':[1,2],
                  'internal_sensor_modes':[0],'controller':'dock parity(y0,y1,y2)'},
        'ready_transition_table':[{'y':list(y),'dock0':step('ready',y,'dock0'),
                                  'dock1':step('ready',y,'dock1'),'wait':'ready'} for y in bits(3)]}
    out['all_assertions_passed']=True
    p=Path(__file__).with_name('docking_cut_discovery_results.json'); p.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
