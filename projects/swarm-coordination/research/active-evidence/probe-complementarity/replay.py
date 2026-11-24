"""Two civil warehouse crews purchase endpoint evidence before a joint move."""
from fractions import Fraction as F
from itertools import product
import json

ACTIONS = ('F', 0, 1)
SETS = tuple(product((False,True), repeat=2))

def run(m, position, buy, old, span, delay, D, actions=None, *,
        bypass=(1,2), reserve=False):
    """Physical event interpreter: fixture pose, old work, probe, read, move."""
    assert m>=2 and 0<=position<=2*m
    x=0
    # Indexed, stable detent positions; physically advance before the duty cut.
    trace=[(-position-1,'home_fixture',0)]
    for t in range(-position-1,-1):
        x+=1
        trace.append((t+1,'detent',x))
    assert x==position
    for i in range(2):
        trace.append((-1,'promise_old_inspection',i,old[i]))
    bypass_old, certify = bypass
    assert 0<=bypass_old<=D and certify>=1
    assert not reserve or bypass_old+certify<=D
    trace.append((-1,'promise_bypass_inspection',bypass_old))
    trace.append((0,'record_probe_booking',buy))
    trace.append((0,'choose_bypass_reservation',reserve))
    ready_bypass=False
    done_bypass_old=0
    complete=[0,0]; scans=[None,None]; evidence_at=[None,None]; use=0
    for t in range(D+1):
        if reserve and t==bypass_old+certify:
            ready_bypass=True
            trace.append((t,'bypass_ready'))
        if t<D and t<bypass_old:
            done_bypass_old+=1
            trace.append((t,'old_bypass_inspection_slot'))
        elif t<D and reserve and bypass_old<=t<bypass_old+certify:
            if t==bypass_old:
                trace.append((t,'decline_optional_bypass_job'))
            trace.append((t,'prepare_bypass_slot'))
        elif not reserve and t<D and t==bypass_old:
            trace.append((t,'serve_optional_bypass_job'))
        for i in range(2):
            if evidence_at[i]==t:
                # The endpoint reader uses global fixture coordinates only in
                # this plant event, not in the crew's decision routine.
                scans[i]=(x==0) if i==0 else (x==2*m)
                trace.append((t,'local_probe_evidence',i,scans[i]))
        if t==D:
            break
        for i in range(2):
            if t<old[i]:
                complete[i]+=1
                trace.append((t,'old_inspection_slot',i))
            elif buy[i] and old[i]<=t<old[i]+span[i]:
                use+=1
                trace.append((t,'exclusive_probe_slot',i))
                if t+1==old[i]+span[i]:
                    # Reading availability is physical completion plus sensing
                    # lag. Completion/delivery in this phase precedes the cut.
                    evidence_at[i]=t+1+delay[i]
    assert complete==list(old) and done_bypass_old==bypass_old
    coarse=[x//2,(x+1)//2]  # mounting of the local optical cell masks
    views=tuple((coarse[i],scans[i]) for i in range(2))
    assert all(not b or s is not None for b,s in zip(buy,scans))
    # Fast move on the lane allowed by the load's actual end/interior stop.
    compatible=int(x in (0,2*m))
    trace.append((D,'private_passive_bins',tuple(coarse)))
    trace.append((D,'locally_usable_views',views))
    if actions is not None:
        chosen=tuple(actions[i][views[i]] for i in range(2))
        for i,a in enumerate(chosen): trace.append((D,'submit_local_command',i,a))
        assert chosen[0]==chosen[1], "unilateral or disagreeing commands"
        mode=chosen[0]
        assert mode=='F' or mode==compatible or (mode=='R' and ready_bypass), "unsafe lane"
        if mode=='R':
            trace.append((D,'use_reserved_bypass'))
        trace.append((D+(2 if mode=='F' else 1),'complete_owed_move',mode))
    return views,compatible,trace,use

def table_policy(rows):
    """Construct connected feasible-component schedules."""
    n=len(rows)
    adjacency=[set() for _ in rows]
    for i in range(n):
        for j in range(i):
            if any(rows[i][0][k]==rows[j][0][k] for k in range(2)):
                adjacency[i].add(j); adjacency[j].add(i)
    todo=set(range(n)); tables=({},{}); fast=set(); components=[]
    while todo:
        p=todo.pop(); members={p}; frontier=[p]
        while frontier:
            for q in adjacency[frontier.pop()] & todo:
                todo.remove(q); frontier.append(q); members.add(q)
        components.append(sorted(members))
        choices={rows[j][1] for j in members}
        a=next(iter(choices)) if len(choices)==1 else 'F'
        if a!='F': fast|=members
        for j in members:
            for i in range(2): tables[i][rows[j][0][i]]=a
    return tables,fast,sorted(components)

def exhaustive_reference(rows, weights, available=ACTIONS):
    """No reachability graph: all pairs of local action tables."""
    left,right=(sorted({r[0][i] for r in rows},key=repr) for i in range(2))
    li={v:k for k,v in enumerate(left)}; ri={v:k for k,v in enumerate(right)}
    best=F(2); valid=0; tables=0
    for aa,bb in product(product(available,repeat=len(left)),product(available,repeat=len(right))):
        tables+=1; loss=F(0)
        for (v,k,*_),p in zip(rows,weights):
            a,b=aa[li[v[0]]],bb[ri[v[1]]]
            if a!=b or (a not in ('F','R') and a!=k): break
            if a=='F': loss+=p
        else:
            valid+=1
            best=min(best,loss)
    return best,valid,tables

def envelope(m,D,old,span,delay,weights,cost,oracle=False,bypass=(1,2)):
    out={}
    for buy in SETS:
        key=''.join(str(int(x)) for x in buy)
        if any(b and o+s+l>D for b,o,s,l in zip(buy,old,span,delay)):
            out[key]=None
            continue
        rows=[run(m,j,buy,old,span,delay,D,bypass=bypass) for j in range(2*m+1)]
        assert len({r[0] for r in rows})==len(rows) # pooled identification
        actions,fast,components=table_policy(rows)
        # Formula independently derived from alternating physical bin cuts.
        expected=(
                  set(range(2*m+1)) if all(buy) else
                  {0} if buy[0] else {2*m} if buy[1] else set())
        assert fast==expected
        loss=1-sum(weights[j] for j in fast)
        count=None
        if oracle:
            ref,_,count=exhaustive_reference(rows,weights)
            assert ref==loss
        for j in range(2*m+1):
            _,_,trace,use=run(m,j,buy,old,span,delay,D,actions,bypass=bypass)
            assert use==sum(s for b,s in zip(buy,span) if b)
            assert trace[-1][0]==D+(1 if j in fast else 2)
        out[key]=dict(fast=sorted(fast),components=components,loss=str(loss),
                      total=str(loss+sum(c for b,c in zip(buy,cost) if b)),table_pairs=count)
    return out

def compare(m,D,old,span,delay,weights,cost,bypass,fee,oracle=False):
    # One exogenous opportunity and old plant for every compared booking.
    entries=envelope(m,D,old,span,delay,weights,cost,oracle=False,bypass=bypass)
    costs={k:F(v['total']) for k,v in entries.items() if v is not None}
    trace=None
    if sum(bypass)<=D:
        rows=[run(m,j,(False,False),old,span,delay,D,bypass=bypass,reserve=True)
              for j in range(2*m+1)]
        tables=tuple({r[0][i]:'R' for r in rows} for i in range(2))
        for j in range(2*m+1):
            _,_,trace,_=run(m,j,(False,False),old,span,delay,D,tables,bypass=bypass,reserve=True)
            assert trace[-1]==(D+1,'complete_owed_move','R')
        if oracle:
            assert exhaustive_reference(rows,weights,(*ACTIONS,'R'))[0]==0
        costs['reserve']=fee
    return ({k:str(v) for k,v in costs.items()},sorted(k for k,v in costs.items() if v==min(costs.values())),trace)

def main():
    w=[F(1,5)]*5; c=(F(1,4),F(1,4))
    main=envelope(2,3,(1,1),(1,1),(1,1),w,c,True)
    assert [main[k]['total'] for k in ('00','10','01','11')]==['1','21/20','21/20','1/2']
    _,_,trace,_=run(2,2,(True,True),(1,1),(1,1),(1,1),3,
                     table_policy([run(2,j,(True,True),(1,1),(1,1),(1,1),3) for j in range(5)])[0])
    # Independently vary duty duration, probe duration, sensor latency and
    # cut, keeping all weights strictly positive.
    sweeps=0
    for m in range(2,8):
        p=[F(j+1,(m+1)*(2*m+1)) for j in range(2*m+1)]
        assert sum(p)==1
        for old,span,delay,D in product(product((1,2),repeat=2), product((1,2),repeat=2),
                                        product((0,1),repeat=2),range(2,6)):
            envelope(m,D,old,span,delay,p,c)
            sweeps+=1
    blocked=envelope(2,3,(2,1),(1,1),(1,1),w,c)
    assert blocked['11'] is None and blocked['10'] is None
    assert min(F(v['total']) for v in blocked.values() if v is not None)==1
    cases={}
    for tag, old, price, held, reserve_fee, best in (
        ('reserve', (1,1), c, (1,2), F(1,3),'reserve'),
        ('both', (1,1), c, (1,2), F(2,3),'11'),
        ('slow', (2,1), c, (2,2), F(1,3),'00'),
        ('single', (1,2), (F(1,10),c[1]), (1,2), F(19,20),'10')
    ):
        costs,opt,example=compare(2,3,old,(1,1),(1,1),w,price,held,reserve_fee,tag=='reserve')
        assert opt==[best]
        cases[tag]=dict(costs=costs,optimum=opt,trace=example)
    print(json.dumps(dict(main=main,reservation_controls=cases,inherited_slot_blocks_A=blocked,
                          paired_policy_tables=sum(v['table_pairs'] for v in main.values()),
                          parameter_sweeps=sweeps, joint_probe_trace=trace),sort_keys=True,indent=1))
if __name__=='__main__': main()
