"""Bounded civil mission and separately verified native source effects."""
from collections import defaultdict
from hashlib import sha1
from itertools import product
from pathlib import Path
import json, subprocess, sys

binary,shared=sys.argv[1:]
core=(Path(shared)/'core.py').read_bytes()
assert sha1(f"blob {len(core)}\0".encode()+core).hexdigest()=="687bf1250c6725992b6de696d0781d7948b4a89e"
sys.path.insert(0,shared)
from core import Event, Row, admitted, view, check, Use

CUT=3
NAMES=('continue','return','reserve','reserve-suppress','continue-qualified')
# Declared directed travel graph and staged catalogue: left/right histories
# share all durations; the late A-contact loss affects the backup, not motion.
graph={('J','I'):1,('I','E'):3,('J','C'):2,('C','I'):3,
       ('J','M'):1,('M','I'):2}
mule_travel={('home','receive'):1,('receive','a'):1,('receive','b'):1,
             ('a','out'):3,('b','out'):3}
def mule_exit(n,loss):
    if n not in (2,3):return CUT     # No deployment from safe home.
    path=('home','receive','b' if loss==1 else 'a','out')
    return CUT+sum(mule_travel[x] for x in zip(path,path[1:]))
routes=(('J','I','E'),('J','C','I','E'),('J','M','I','E'),('J','M','I','E'),('J','I','E'))
DUE={'report':6,'inspection':6,'exit':10,'mule-safe':10,'independent':8}
qname=('lane','reserve')
RF=lambda s: ('tx',s)
RX=lambda s: ('rx',s)
def route(n):
    t=CUT
    visited={'J':t}
    path=routes[n]
    for a,b in zip(path,path[1:]):
        t+=graph[a,b]
        visited[b]=t
    return visited

def radio(cases):
    inp=''.join(' '.join(map(str,p))+'\n' for p in cases)
    out=subprocess.run([binary],input=inp,text=True,check=True,capture_output=True).stdout
    rows=[tuple(map(int,l.split())) for l in out.splitlines()]
    assert len(rows)==len(cases)
    return dict(zip(cases,rows))

def expected(p,n):
    paid,notice,loss=p
    if n==4 and paid and notice==0:return -1,0,0,0
    if n in (0,4):return 7,2,0,1
    if n==1:return 5,2,0,1
    if n==3 and paid:return -1,0,0,0
    if loss in (2,3):return -1,2,0,0
    return 6,4,1,1

def model(p,blob,reserve_budget):
    paid,notice,loss=p
    common=blob[p+(0,)]
    old_rx,obs=common[:2]
    assert old_rx==1
    base=[Event(0,0,uses=(Use(RF('P'),2,5,8),Use(RX('Base'),2,5,8))),
          Event(8,0,paid=('independent',) if common[7]==1 else (),
                    uses=(Use(RF('Independent'),1,5,8),Use(RX('Far'),1,5,8)))]
    if paid:base.append(Event(1,0,paid=('report',)))
    # Both candidates dispatch the same one-byte terminal signal attempt.
    delivered=common[8]==1
    signal_at=4 if notice==2 else 2
    base.append(Event(signal_at,3,uses=(Use(RF('Owner'),1,5,8),
                                       Use(RX('Control'),1,5,8,delivered))))
    rec=((2,'lead',('known-terminal',obs)),) if obs>=0 else ()
    opts={}
    for n,name in enumerate(NAMES):
        _,_,finish,applied,extra,mule,reach,work,_,switch=blob[p+(n,)]
        assert work==1
        rr=route(n)
        times={'inspection':rr['I'],'exit':rr['E']}
        acts=[Event(t,2,paid=(k,)) for k,t in times.items()]
        if n in (2,3):
            acts.append(Event(4,2,uses=(Use(qname,1,reserve_budget,8),
                                        Use(RF('Gate'),1,5,8),
                                        Use(RX('Q'),1,5,8,bool(switch)))))
            if extra:
                who='RelayB' if loss==1 else 'RelayA'
                acts.append(Event(5,0,uses=(Use(RF('Q'),2,5,8),Use(RX(who),2,5,8,bool(mule)))))
                if mule:acts.append(Event(6,0,uses=(Use(RF(who),2,5,8),Use(RX('Base'),2,5,8,bool(reach)))))
        elif extra:
            acts.append(Event(5 if n==1 else 7,0,uses=(Use(RF('P'),2,5,8),Use(RX('Base'),2,5,8,bool(reach)))))
        if not paid and applied:
            acts.append(Event(finish,1,paid=('report',)))
        acts.append(Event(mule_exit(n,loss),4,paid=('mule-safe',)))
        opts[name]=tuple(acts)
    return Row(rec,frozenset(),tuple(base),opts)

def compare(p,n,res):
    # Independent symbolic schedule, idempotent terminal effects and budget.
    paid,notice,loss=p
    done,extra,mu,rx=expected(p,n)
    final=1 if paid else done
    rr=route(n)
    return rr['I']<=6 and rr['E']<=10 and mule_exit(n,loss)<=10 and 0<=final<=6 and (n not in (2,3) or res>=1)

def achord_cut(backlog,upper,lower,already_returning):
    # Source projection of the movement trigger only. The experiment
    # is before either exit or timeout; entry and exit share the same
    # observed backlog in the paired cases. There is one strong
    # reachable comms checkpoint in this miniature.
    assert lower<=upper
    return 1 if (backlog>=lower if already_returning else backlog>upper) else 0

def options_by_view(rows,names):
    return admitted(rows,'lead',CUT,DUE,names)

def main():
    cases=list(product(range(2),range(4),range(4),range(5)))
    results=radio(cases)
    for (paid,notice,l,n),z in results.items():
        t,extra,mu,rx=expected((paid,notice,l),n)
        done=1 if paid else t
        obs=paid if notice==0 else -1
        assert z==(1,obs,done,int(done>=0),extra,mu,rx,1,int(notice!=1),int(n in (2,3) and l!=3)),((paid,notice,l,n),z)
    evals=0
    for p,res in product(product(range(2),range(4),range(4)),range(2)):
        row=model(p,results,res)
        for j,a in enumerate(NAMES):
            assert check(row,a,CUT,DUE)==compare(p,j,res)
            evals+=1

    # Positive compound contact family: common path already blocked, then
    # at the staging site either ordinary contact A or backup B is usable.
    def scenarios(allowed_notices,losses=(0,1),res=1):
        return [(p,model(p,results,res)) for p in product(range(2),allowed_notices,losses)]
    good=scenarios((0,))
    available=options_by_view([x[1] for x in good],NAMES)
    assert all(available.values())
    def plan_cost(p,a):
        j=NAMES.index(a)
        # A complete priority statement: after mandatory safety/service,
        # minimize one nonreusable physical staging commitment per mission.
        return int(j in (2,3)),results[p+(j,)][4]+int(j in (2,3))
    def robust_pick(rows,opts):
        cohorts=defaultdict(list)
        for p,row in rows:cohorts[view(row,'lead',CUT)].append(p)
        return {o:min(ops,key=lambda a:(max(plan_cost(p,a) for p in cohorts[o]),a!='reserve-suppress'))
                for o,ops in opts.items() if ops}
    chosen=robust_pick(good,available)
    assert set(chosen.values())=={'continue-qualified','reserve-suppress'}
    for p,row in good:
        assert check(row,chosen[view(row,'lead',CUT)],CUT,DUE)

    # Any policy using only this fixed movement trigger fails at least one
    # hard duty. Sweep every distinct threshold behavior, include old
    # hysteresis state and different map/rate projections held constant
    # within each pair. The timeout cannot occur prior to the decision.
    trials=0
    for backlog,upper,lower,was in product((199,200,256,300,301,320),range(0,401,5),range(0,401,5),range(2)):
        if lower>upper:continue
        option=achord_cut(backlog,upper,lower,was)
        assert not all(compare(p,option,1) for p,_ in good)
        trials+=1
    literal=[]
    for backlog in (256,320):
        j=achord_cut(backlog,300,200,False)
        literal.append([backlog,NAMES[j],int(sum(compare(p,j,1) for p,_ in good))])
    # A stronger aggregate-selected route menu may always preposition a
    # mule and suppress an unnecessary send at the handler. Give it this
    # best route instead of pretending the whole ACHORD limitation.
    constant=[j for j in range(5) if all(compare(p,j,1) for p,_ in good)]
    assert constant==[2,3]
    late=scenarios((0,1,2,3))
    late_opt=options_by_view([x[1] for x in late],NAMES)
    assert set(late_opt[()])=={'reserve','reserve-suppress'}
    blocked=scenarios((0,),losses=(0,1,2))
    bopts=options_by_view([x[1] for x in blocked],NAMES)
    assert bopts[((2,('known-terminal',0)),)]==()
    mute=scenarios((0,),losses=(0,1,3))
    assert options_by_view([x[1] for x in mute],NAMES)[((2,('known-terminal',0)),)]==()
    zero=scenarios((0,),res=0)
    assert options_by_view([x[1] for x in zero],NAMES)[((2,('known-terminal',0)),)]==()

    # Exhaustive matched direct control choosing routes by identical local
    # receipt before the commitment. The reference may branch the same way.
    local_direct={}
    for p,row in good:
        o=view(row,'lead',CUT)
        g=[q for q,qr in good if view(qr,'lead',CUT)==o]
        feasible=[j for j in range(5) if all(compare(q,j,1) for q in g)]
        j=min(feasible,key=lambda j:(max(plan_cost(q,NAMES[j]) for q in g),j!=3))
        local_direct[o]=NAMES[j]
    assert local_direct==chosen
    executions=[]
    for p,row in good:
        with subprocess.Popen([binary],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as native:
            native.stdin.write(' '.join(map(str,p))+' -1\n')
            native.stdin.flush()
            label,obs=native.stdout.readline().split()
            assert label=='terminal'
            raw=int(obs)
            receipt=() if raw<0 else ((2,('known-terminal',raw)),)
            name=chosen[receipt]
            j=NAMES.index(name)
            native.stdin.write(f'{j}\n')
            native.stdin.flush()
            got=tuple(map(int,native.stdout.readline().split()))
            native.stdin.close()
            assert native.wait(timeout=5)==0
            assert got==results[p+(j,)]
            executions.append([p,name,got[2],got[4],got[-1]])
    scored=[]
    for p,row in good:
        literal=chosen[view(row,'lead',CUT)]
        scored.append({'fault':p,'direct_tie':literal,'new':plan_cost(p,literal),
                       'aggregate':plan_cost(p,'reserve-suppress'),
                       'new_service':[results[p+(NAMES.index(literal),)][2],route(NAMES.index(literal))['I'],
                                      route(NAMES.index(literal))['E']],
                       'aggregate_service':[results[p+(3,)][2],route(3)['I'],route(3)['E']]})
    # Even with a free later receipt, none of the catalogue routes can
    # start one tick after cut and still meet both hard due times if unpaid.
    for j in range(5):
        timing=route(j)
        if timing['I']+1<=6:
            report,_,_,_=expected((0,0,0),j)
            assert report+1>6
    print(json.dumps({'native_cases' :len(cases),'core_direct_checks':evals,
          'threshold_trials':trials,'selected_native_executions':executions,'documented_parameters':[
              [b,NAMES[achord_cut(b,300,200,False)]] for b in (256,320)],
          'paired_positive':scored,'no_receipt':late_opt[()],
          'reserve_available':True,'positive_scope_excludes_both_links_lost_or_decisive_switch_read_erasure':True},
          indent=2,sort_keys=True))
if __name__=='__main__':main()
