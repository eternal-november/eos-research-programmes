"""Selected native receive debit plus exact stationary capture/ongoing motion."""
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
from subprocess import run
import json
import motion as m

TICKS=1024
OFFSET=1024
CEIL=lambda x:-((-x.numerator)//x.denominator)
FLOOR=lambda x:x.numerator//x.denominator
def setups():
    near_q=F(17,40);near_defer=m.RGOOD;k=m.A*m.SHI
    assert m.test(m.SHI,0,F(42,100),near_q,near_defer)
    near_start=m.S-F(5,2)*m.SHI
    assert near_start>=near_q
    near_pref=[(near_start,0),(near_start+m.SHI/2,-m.A),
               (near_start+m.SHI,0),(near_defer,m.A)]
    nf=m.trace(near_pref+[(m.S+(1-k)/m.A,m.A),(2,0)])
    x,v=m.at(m.trace(near_pref+[(m.C,-m.A)]),m.C)
    assert x<=4 and v<0
    nl=m.trace(near_pref+[(m.C,-m.A),(m.C-v/m.A,m.A),(2,0)])
    assert m.at(nf,2)[0]>=m.H-1
    assert m.at(nf,near_q)==m.at(nl,near_q)==(4,0)

    zlo=F(14340554,10**8);zhi=F(14340555,10**8)
    far_q=m.S-F(3,20);far_defer=m.S+(zlo-F(1,2))/m.A
    pastq=m.S+(zhi-F(1,2))/m.A
    assert zlo*zlo<m.A*m.DELTA<zhi*zhi
    assert FLOOR(pastq*TICKS)==FLOOR(far_defer*TICKS)
    prep=[(F(1,10),-m.A),(F(1,5),m.A),(far_q,0)]
    fb=far_defer-(far_q+1/m.A)
    ff=m.trace(prep+[(far_q+1/m.A,m.A),(far_defer,-m.A),(far_defer+fb,m.A),(2,0)])
    fl=m.trace(prep+[(far_q+1/m.A,m.A),(far_q+2/m.A,-m.A),(2,0)])
    assert m.at(ff,far_q)==m.at(fl,far_q)==(F(39,10),0) and m.at(ff,2)[0]>=m.H-1
    assert FLOOR(m.RGOOD*TICKS)==FLOOR(m.RBAD*TICKS)
    return {'near':(near_q,near_defer,nf,nl),'far':(far_q,far_defer,ff,fl)}

def broker_oracle(cap,sched):
    tx={k:[] for k in 'PQ'};rx=[];verdict=[]
    def live(hist,t):return sum(n for u,n in hist if t-u<=TICKS)
    for t,c,p in sched:
        n=len(p);out='-'
        if live(tx[c],t)+n<=cap:
            tx[c].append((t,n))
            if live(rx,t)+n<=cap:
                rx.append((t,n));out=c+':'+p
        verdict.append(out)
    return verdict

def main():
    cfg=setups();scenarios=[]
    for site,world,cap,old_at,policy in product(cfg,('L','F'),(2,3),range(-430,-397),
                                                 ('first-sufficient','boundary-only','blind-fixed')):
        q,r,*_=cfg[site]
        first=CEIL(q*TICKS);last=FLOOR(r*TICKS)
        expire=old_at+TICKS+1
        if policy=='first-sufficient':ticks=(first if cap>=3 else max(first,expire),)
        elif policy=='boundary-only':ticks=(max(first,expire-1),)
        else:ticks=(600,)
        a=[(old_at+OFFSET,'P','OK')] # actual old receipt must not move or disappear
        a += [(t+OFFSET,'Q',world) for t in ticks]
        scenarios.append((site,world,cap,old_at,policy,first,last,a))
    inp=[]
    for _,_,c,_,_,_,_,a in scenarios:
        inp.append(f'{c} {len(a)}');inp.extend(f'{t} {s} {p}' for t,s,p in a)
    rows=run(['./broker'],input='\n'.join(inp)+'\n',text=True,check=True,capture_output=True).stdout.splitlines()
    assert len(rows)==len(scenarios)
    matches=0;paths=0;table={};branches={}
    for (site,world,c,old,policy,first,last,a),line in zip(scenarios,rows):
        n,*out=line.split()
        assert int(n)==len(a) and out==broker_oracle(c,a) and out[0]=='P:OK'
        matches+=1
        effect=next((a[i][0]-OFFSET for i,d in enumerate(out) if d==f'Q:{world}'),None)
        qualified=effect is not None and first<=effect<=last
        if policy=='first-sufficient':
            # existence among all legal send slots, not a guess from the chosen schedule
            other=any(broker_oracle(c,[a[0],(t+OFFSET,'Q',world)])[-1]!='-' for t in range(first,last+1))
            assert qualified==other==(c>=3 or old+TICKS+1<=last)
        if policy=='boundary-only' and c==2:assert effect is None
        if qualified:
            chosen=cfg[site][2 if world=='F' else 3]
            key=(site,world)
            if key not in branches:
                branches[key]=m.verify(chosen,'far' if world=='F' else 'late')
            assert F(effect,TICKS)<=cfg[site][1]
            paths+=1
        table[site,c,old,policy]=qualified
    for old,expected in ((-421,(True,True)),(-411,(True,False)),(-401,(False,False))):
        assert tuple(table[s,2,old,'first-sufficient'] for s in ('near','far'))==expected
    laws=(dict(early_near=1,mid_far=1),dict(early_far=1,mid_near=1))
    def successes(law):
        return sum(int(table[site,2,{'early':-421,'mid':-411}[stage],'first-sufficient'])*weight
                   for k,weight in law.items() for stage,site in (k.split('_'),))
    assert list(map(successes,laws))==[1,2]
    print(json.dumps({'cases':matches,'qualified_controls':paths,
          'physical_extrema':sum(branches.values()),'same_half_marginals_success_per_two':[1,2],'near_last_tick':619,'far_last_tick':606,
          'last_old_tick_cap2_near':-406,'last_old_tick_cap2_far':-419,
          'one_extra_byte_handles_every_old_tick':all(table[s,3,o,'first-sufficient'] for s in cfg for o in range(-430,-397))},
          separators=(',',':'),sort_keys=True))
if __name__=='__main__':main()
