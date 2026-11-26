"""Join held-in cave routes to actual hosted-reader effect traces."""
from collections import defaultdict
from importlib.util import spec_from_file_location,module_from_spec
from itertools import product
from pathlib import Path
import json,subprocess,sys

cops,shared,cave,bin,old=map(Path,sys.argv[1:6])
spatial_args=sys.argv[6:]
sys.path.insert(0,str(cave))
# Reuse the pinned prior framework without calling its CLI.
sys.argv[:]=[sys.argv[0],str(cops),str(shared)]
spec=spec_from_file_location('prior_cave',cave/'replay.py')
native=module_from_spec(spec)
spec.loader.exec_module(native)
old_fixture=native.fixture
def extended(*case):
    m,q,e=old_fixture(*case)
    return m+(('M','K'),('K','U'),('K','G'),('K','M')),q,e
native.fixture=extended
native.NODES+=('K',)
from core import Event,Row,Use,admitted

CUT=9
NAMES=('near','far','shared','dedicated','quiet')
DUE={'old-clear':19,'report':12,'new-inspection':12,'scout-safe':13,
     'mule-safe':14,'independent':13}
NATIVE_BRANCH=(0,1)
CONTINUATIONS=tuple(product((0,1,2),repeat=3))
PLANS=tuple(product(range(5),CONTINUATIONS))
POS=('M','W','J','K','J')
def tx(s):return ('tx',s)
def rx(s):return ('rx',s)
def radio_use(k,bytes,deposit=True):return Use(k,bytes,5,8,deposit)

def physical(hold):
    rows=subprocess.run([sys.executable,'-B',str(old),*spatial_args,str(hold)],
                        text=True,check=True,capture_output=True).stdout
    return {(x['side'],x['case']):x for x in json.loads(rows)}

def packet_controls():
    args=tuple(product(range(5),range(2),range(2),range(2),range(3)))
    dat=''.join(' '.join(map(str,p))+'\n' for p in args)
    r=subprocess.run([bin],input=dat,text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(r)==len(args)
    result={}
    for (m,b,rq,cu,choice),line in zip(args,r):
        probe=m in (2,3)
        request=int(probe and not rq)
        observed=b if request and not cu else -1
        legal=int(choice==m if m<2 else (not probe or request) and choice<2)
        out=tuple(map(int,line.split()))
        expected=request,int(m==2 and request),observed,int(legal and choice==b),1,legal,int(observed>=0)
        assert out==expected,((m,b,rq,cu,choice),out,expected)
        result[m,b,rq,cu,choice]=out
    return result

def shape(m,b,choice):
    return choice==b if m>=2 else choice==m==b

def direct(plain,k,m,b,rq,cu,choice,reserve):
    active=m in (2,3) and not rq
    old_end=plain[k]['physical_relocation']
    old_end+=int(m==2 and active and old_end>10)
    return (old_end<=19 and (m!=3 or reserve>=1) and
            (m not in (2,3) or active) and shape(m,b,choice))

def model(k,b,rq,cu,res,tapes,pack):
    opts={}
    early=tapes[0][k]['physical_relocation']
    prefix=(Event(early,0,paid=('old-clear',)),) if early<CUT else ()
    for m,table in PLANS:
        _,_,see,*_=pack[m,b,rq,cu,2]
        choice=table[see+1]
        req,held,obs,pay,unrelated,legal,heard=pack[m,b,rq,cu,choice]
        assert see==obs
        w=tapes[held][k]
        # This old duty follows the actual selected physical branch, not
        # whether the current actor received its answer.
        if early<CUT:assert early==w['physical_relocation'] and w['actual_due_paid']
        events=[Event(12,1,paid=('new-inspection',)),Event(13,1,paid=('scout-safe',)),
                Event(13,2,paid=('independent',) if unrelated else ()),
                Event(14,2,paid=('mule-safe',))]
        if not prefix:
            events.append(Event(w['physical_relocation'],0,
                                paid=('old-clear',) if w['actual_due_paid'] else ()))
        usages=[]
        if m==3:usages.append(Use(('lane','dedicated'),1,res,8))
        if m in (2,3):
            usages.extend((radio_use(tx('staff'),1),radio_use(rx('gate'),1,bool(req))))
        if usages:events.append(Event(CUT,1,uses=tuple(usages)))
        if req:
            events.append(Event(10,3,uses=(radio_use(tx('source'),1),radio_use(rx('mule'),1,bool(heard)))))
        if legal:events.append(Event(11,1,uses=(radio_use(tx('scout'),2),radio_use(rx('mule'),2,bool(pay)))))
        if pay:events.append(Event(12,3,uses=(radio_use(tx('mule'),2),radio_use(rx('base'),2)),paid=('report',)))
        opts[m,table]=tuple(events)
    return Row((),frozenset(),prefix,opts)

def main():
    plain=physical(0); held=physical(1); p=packet_controls()
    assert set(plain)==set(held) and len(plain)==10
    for k in plain:
        t=plain[k]['physical_relocation']
        assert held[k]['physical_relocation']==t+int(t>10)
        assert held[k]['host_idle']==1
    # Run actual COPS and its separate graph search on the recovery
    # projection, without using a future branch at the first decision.
    bchecks=0
    for m,b,c in product(range(5),range(2),range(2)):
        p0=(1,1,b,1)
        pos=('U','G')[c]
        solved=native.call(p0,3,first=POS[m],second=pos)
        yes=shape(m,b,c)
        assert (solved is not None)==yes and native.reference(p0,3,first=POS[m],second=pos)==yes
        if yes:
            poses,comm=solved
            assert poses['mule'][1]==POS[m] and poses['mule'][2]==pos
            assert ('Y',pos,'scout') in comm[2] and ('Z','B','scout') in comm[3]
        bchecks+=1

    banks={}
    indexed={}
    evals=0
    from core import check
    for k,b,rq,cu,res in product(plain,range(2),range(2),range(2),range(2)):
        row=model(k,b,rq,cu,res,(plain,held),p)
        yes=[]
        for m,table in PLANS:
            see=p[m,b,rq,cu,2][2]
            a=table[see+1]
            good=direct(plain,k,m,b,rq,cu,a,res)
            actual=check(row,(m,table),CUT,DUE)
            assert actual==good,(k,b,rq,cu,res,m,table,a,actual,good)
            if good:yes.append((m,table))
            evals+=1
        indexed[k,b,rq,cu,res]=row,set(yes)

    for name,keys in [('slack',[k for k in plain if plain[k]['physical_relocation']<=18]),
                      ('tight',[k for k in plain if plain[k]['physical_relocation']==19]),
                      ('unqualified',list(plain))]:
        for res,drop in product(range(2),range(3)):
            fail=((0,0),) if drop==0 else ((0,0),(0,1)) if drop==1 else ((0,0),(1,0))
            pop=[indexed[k,b,rq,cu,res] for k,b,(rq,cu) in product(keys,range(2),fail)]
            a=admitted([x[0] for x in pop],'crew',CUT,DUE,PLANS)[()]
            d=set.intersection(*(x[1] for x in pop))
            assert set(a)==d
            accepted=sorted({m for m,_ in a})
            expectation=(([2] if name=='slack' else [])+([3] if res else [])) if drop==0 else []
            assert accepted==expectation,(name,res,drop,accepted)
            banks[name,res,drop]=[NAMES[m] for m in accepted]
    badk=next(k for k in plain if plain[k]['physical_relocation']==19)
    goodk=next(k for k in plain if plain[k]['physical_relocation']==18)
    assert p[2,0,0,1,2][:3]==(1,1,-1) and held[badk]['physical_relocation']==20

    staged=[]
    for k,m,b,cu in [(goodk,2,0,0),(badk,3,1,0),(badk,2,1,1),(badk,2,0,0)]:
        tag='forced-negative' if m==2 and k==badk else 'admitted'
        with subprocess.Popen([bin],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) as q:
            q.stdin.write(f'{m} {b} 0 {cu} -1\n')
            q.stdin.flush()
            t,h=q.stdout.readline().split()
            assert t=='hold'
            selected=physical(int(h))[k]
            q.stdin.write('1\n');q.stdin.flush()
            t,v=q.stdout.readline().split()
            assert t=='view'
            rr=int(v)
            # The online second choice reads no hidden original branch or
            # future warehouse completion. The shadow negative still runs
            # to measure physical harm if the unsupported prefix issued.
            choice=rr if tag=='admitted' and rr>=0 else 2
            q.stdin.write(str(choice)+'\n');q.stdin.flush()
            got=tuple(map(int,q.stdout.readline().split()))
            q.stdin.close()
            assert q.wait(timeout=10)==0
        assert got==p[m,b,0,cu,choice]
        assert got[3]==(tag=='admitted') and got[4]==1
        assert (selected['physical_relocation']<=19)==(tag=='admitted')
        staged.append([tag,m,b,cu,rr,selected['physical_relocation'],got[3]])
    print(json.dumps(dict(native_cops_cases=bchecks,native_packet_controls=len(p),
          native_warehouse_cases=len(plain)+len(held),whole_comparisons=evals,
          first_actions={str(k):v for k,v in banks.items()},staged=staged),
          sort_keys=True,indent=2))
if __name__=='__main__':main()
