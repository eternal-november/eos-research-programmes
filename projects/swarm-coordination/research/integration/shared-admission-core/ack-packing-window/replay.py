"""Paired native payload, carried debt and timing check at the reply boundary."""
from itertools import product
from dataclasses import replace
import json,subprocess,sys
wire,core,old,*paths=sys.argv[1:]
sys.path.insert(0,core)
from core import Event,Row,Use,admitted,check

CUT=9
DUE={'prefix':8,'prior-effect':19,'new-reply':12,'old-report':14,'unrelated':15}
def key(layer,name):return (layer,name)
def u(layer,node,n,b=True):return Use(key(layer,node),n,5,8,b)

def data(params):
    out=subprocess.run([wire],input=''.join(' '.join(map(str,p))+' 0\n' for p in params),
                       text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(out)==len(params)
    return {p:tuple(map(int,z.split())) for p,z in zip(params,out)}

def reference(p):
    m,aS,aR,dS,dR,eA,eD,need,stale,y,b=p
    recvA=int(m==1 and not eA)
    recvD=1-eD
    early=y if (recvA or (m==2 and recvD)) and not stale else -1
    both=recvD and (early>=0 if m==1 else not stale)
    Y=y if both or early>=0 else -1
    B=b if both else -1
    held=int(need and early<0)
    tx=2+aS*int(m==1)+dS
    rx=2+aR*recvA+dR*recvD
    return recvA,recvD,early,Y,B,held,tx,rx,int(max(tx,rx)<=3),1,1

def replay_old(hold):
    a=subprocess.run([sys.executable,'-B',old,*paths,str(hold)],text=True,capture_output=True,check=True).stdout
    return {(r['side'],r['case']):r['physical_relocation'] for r in json.loads(a)}

def reply_slot(t,order,aliasS,aliasR,received):
    return Event(t,order,uses=(u('tx','P' if aliasS else 'Q',1),
                               u('rx','Base' if aliasR else 'Second',1,bool(received))))

def build(base,wc,params,outputs,options):
    common=[Event(8,0,uses=(u('tx','P',2),u('rx','Base',2)),paid=('prefix',)),
            Event(15,0,uses=(u('tx','Independent',1),u('rx','Far',1)),paid=('unrelated',))]
    if base<CUT:common.append(Event(base,0,paid=('prior-effect',)))
    f={}
    for name in options:
        p=params(name)
        m,aS,aR,dS,dR,eA,eD,need,stale,y,b=p
        aa,dd,early,Y,B,held,tx,rx,carried,_,_=outputs[p]
        branch_end=wc[held]
        events=[]
        if base>=CUT:events.append(Event(branch_end,0,paid=('prior-effect',)))
        else:assert branch_end==base
        if m==1:events.append(reply_slot(10,1,aS,aR,aa))
        last=10 if m==2 else 12
        events.append(reply_slot(last,1,dS,dR,dd))
        if (Y,B)==(y,b):events.append(Event(last,2,paid=('new-reply',)))
        events.append(Event(14,1,uses=(u('tx','P',2),u('rx','Base',2))))
        # Infeasible due to budget in oracle goes through identical debit
        # check, not a retrospectively granted mandatory completion.
        if carried:events.append(Event(14,2,paid=('old-report',)))
        f[name]=tuple(events)
    return Row((),frozenset(),tuple(common),f)

def main():
    params=tuple(product(range(3),*(range(2) for _ in range(10))))
    got=data(params)
    assert all(got[p]==reference(p) for p in params)
    idle=tuple(replay_old(h) for h in range(2))
    assert set(idle[0])==set(idle[1]) and len(idle[0])==10
    for k,a in idle[0].items():assert idle[1][k]==a+int(a>10)
    checks=0
    # Four raw ledger placements. The spare authorized early lane is a
    # separate input, not available to one policy by convention only.
    NAMES=('pack','split','spare','early-join')
    grids={}
    for k,place,eA,eD,need,stale,spare,ready in product(idle[0],tuple(product(range(2),repeat=4)),*(range(2) for _ in range(6))):
        aS,aR,dS,dR=place
        def ps(n):return ((2 if n=='early-join' else int(n!='pack')),aS if n!='spare' else 0,
                          aR if n!='spare' else 0,dS,dR,eA,eD,need,stale,1,1)
        menu=NAMES[:2]+(('spare',) if spare else ())+(('early-join',) if ready else ())
        w=tuple(t[k] for t in idle)
        row=build(w[0],w,ps,got,menu)
        feasible=set()
        for n in NAMES:
            r=reference(ps(n))
            ok=n in menu and r[3:5]==(1,1) and w[r[5]]<=19 and r[8]==1
            assert check(row,n,CUT,DUE)==ok,(k,place,eA,eD,need,stale,spare,n)
            if ok:feasible.add(n)
            checks+=1
        grids[k,place,eA,eD,need,stale,spare,ready]=(row,feasible)

    tight=next(k for k,t in idle[0].items() if t==19)
    slack=next(k for k,t in idle[0].items() if t==18)
    def region(k,place,need,spare,ready=0):
        return grids[k,place,0,0,need,0,spare,ready]
    def single(k,place,need,spare,ready=0):return sorted(region(k,place,need,spare,ready)[1])
    assert single(tight,(1,1,1,1),0,0)==['pack']
    assert single(tight,(0,0,0,0),1,0)==['split']
    assert single(tight,(1,1,1,1),1,0)==[]
    assert single(tight,(1,1,1,1),1,1)==['spare']
    assert single(tight,(1,1,1,1),1,0,1)==['early-join']
    assert single(slack,(1,1,1,1),1,0)==['pack']
    # Same final fields, physically different prelude. Both get all
    # final content without interference, yet only the early path works.
    def both(n,alias,required):
        return (n,alias,alias,alias,alias,0,0,required,0,1,1)
    assert got[both(0,0,1)][3:5]==got[both(1,0,1)][3:5]==(1,1)
    assert got[both(0,0,1)][5]==1 and got[both(1,0,1)][5]==0
    # Distinct ledger loss: erased aliased Prelude still puts P over
    # its post-tail cap but no longer congests the receiver.
    tx_lost=got[1,1,1,1,1,1,0,0,0,1,1]
    assert tx_lost[6:9]==(4,3,0)
    rx_lost=got[1,0,1,0,1,1,0,0,0,1,1]
    assert rx_lost[6:9]==(2,3,1)
    # With neither law nor sufficient shared view at the first cut,
    # choosing “whichever works” per world is not a realizable plan.
    x=region(tight,(1,1,1,1),0,0);y=region(tight,(0,0,0,0),1,0)
    assert x[1] and y[1] and not x[1].intersection(y[1])
    assert admitted([x[0],y[0]],'lead',CUT,DUE,NAMES)[()]==()

    mixed=[region(tight,(1,1,1,1),0,1)[0],
           region(tight,(0,0,0,0),1,1)[0]]
    with_spare=admitted(mixed,'lead',CUT,DUE,NAMES)[()]
    assert with_spare==('spare',)
    def notices(at):
        return [replace(row,receipts=((at,'lead',('early-consumer',i)),))
                for row,i in zip(mixed,range(2))]
    resolved=admitted(notices(CUT),'lead',CUT,DUE,NAMES)
    assert set(resolved.values())=={('pack','spare'),('split','spare')}
    assert admitted(notices(CUT+1),'lead',CUT,DUE,NAMES)[()]==with_spare

    # Same native packet process stays alive while separate exact old
    # simulator reruns are selected by the actual prelude callback.
    inline=[]
    for p in [(0,1,1,1,1,0,0,0,0,1,0),(1,1,1,1,1,0,0,0,0,1,0),
              (0,0,0,0,0,0,0,1,0,0,1),(1,0,0,0,0,0,0,1,0,0,1),
              (1,0,0,0,0,1,0,1,0,1,0),(1,0,0,0,0,0,0,1,1,1,0),(2,1,1,1,1,0,0,1,0,1,0)]:
        with subprocess.Popen([wire],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as q:
            q.stdin.write(' '.join(map(str,p))+' 1\n');q.stdin.flush()
            tag,h,b=q.stdout.readline().split()
            assert tag=='prior'
            t=replay_old(int(h))[tight]
            q.stdin.write('1\n');q.stdin.flush()
            z=tuple(map(int,q.stdout.readline().split()))
            q.stdin.close()
            assert q.wait(timeout=8)==0
        assert z==got[p] and int(h)==z[5] and int(b)==z[2]
        inline.append([p,t,z[3:9]])
    print(json.dumps(dict(native_cases=len(params),whole_checks=checks,inline=inline,
          cases=dict(pure_alias=single(tight,(1,1,1,1),0,0),
              required_disjoint=single(tight,(0,0,0,0),1,0),
              required_shared=single(tight,(1,1,1,1),1,0),
              required_shared_spare=single(tight,(1,1,1,1),1,1),
              required_shared_early_data=single(tight,(1,1,1,1),1,0,1),
              required_shared_slack=single(slack,(1,1,1,1),1,0)),
          same_last_fields_not_same_old_effect=True,same_view_no_common=True,
          before_cut_view_allows_ordinary=sorted([list(x) for x in resolved.values()]),
          late_or_missing_requires_spare=with_spare),
          indent=2,sort_keys=True))
if __name__=='__main__':main()
