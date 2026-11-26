from fractions import Fraction as F
from itertools import product
import json

def atoms(p,q,s,authority):
    assert authority in ('unchanged','prospective') and 0<s<=q*min(p,1-p)
    out=[]
    for t,pt in enumerate((p,1-p)):
        obs=t if authority=='prospective' else 1
        out.extend([(s,1,t,True,obs),(q*pt-s,1,t,False,obs),((1-q)*pt,0,t,False,obs)])
    assert sum(m for m,*_ in out)==1 and min(m for m,*_ in out)>=0
    return out

def direct(a, bit, x):
    old=new=union=service=early_new=F(0)
    for mass,O,t,H,obs in a:
        for dispatch,prob in [(True,x[obs]),(False,1-x[obs])]:
            m=mass*prob
            N=dispatch and H and t==bit
            old+=m*O
            new+=m*N
            early_new+=m*(N and obs==0)
            union+=m*(O or N)
            service+=m*(dispatch and not N)
    return old,new,union,service,early_new

def policy(p,s,cap,known,scope):
    l=min(F(1),cap/s)
    allowed=(0,1) if known is None else (known,)
    limited=set(allowed) & ({0} if scope=='receipt' else {0,1})
    x=tuple(l if b in limited else F(1) for b in (0,1))
    worst=p*x[0]+(1-p)*x[1]-s*max(x[b] for b in allowed)
    return x,worst

grids=0
boundaries=0
grid=tuple(F(i,8) for i in range(9))
for p,q in product([F(1,4),F(1,2),F(3,4),F(2,5)],[F(1,4),F(1,3),F(1,2)]):
    for s in [q*min(p,1-p), q*min(p,1-p)/2]:
        a=atoms(p,q,s,'prospective')
        u=atoms(p,q,s,'unchanged')
        found=[]
        for x in product(grid,repeat=2):
            z=[direct(a,b,x) for b in (0,1)]
            z0=direct(u,0,x)
            assert z0==(q,s*x[1],q,(1-s)*x[1],F(0))
            for b,(old,new,union,service,early) in enumerate(z):
                assert (old,new,union,service,early)==(q,s*x[b],q,p*x[0]+(1-p)*x[1]-s*x[b],s*x[0] if b==0 else 0)
                grids+=1
            found.append(z)
        for l in grid+(F(2),):
            for known,scope in product((None,0,1),('issue','receipt')):
                cap=s*l
                x,opt=policy(p,s,cap,known,scope)
                admissible=(0,1) if known is None else (known,)
                row=1 if scope=='issue' else 4
                actual=max(min(z[b][3] for b in admissible)
                           for z in found if all(z[b][row]<=cap for b in admissible))
                assert actual==opt
                assert all(direct(a,b,x)[row]<=cap for b in admissible)
                boundaries+=1

word_checks=0
sizes={}
p,q,s=F(1,2),F(1,4),F(1,8)
a=atoms(p,q,s,'prospective')
for m in range(1,9):
    profiles=set()
    for law in range(1<<m):
        decisions=[]
        for i in range(m):
            b=(law>>i)&1
            assert direct(a,b,(1,1))[:3]==(q,s,q)
            assert direct(a,b,(0,0))[:3]==(q,F(0),q)
            # A prospective cap s/2 reads which receipt cell carries
            # the new failure. The original union verdict is identical.
            decisions.append(direct(a,b,(1,0))[1]<=s/2)
            word_checks+=1
        profiles.add(tuple(decisions))
    assert len(profiles)==1<<m
    sizes[m]=len(profiles)

witness={}
for b,scope in product((None,0,1),('issue','receipt')):
    x,v=policy(p,s,F(1,16),b,scope)
    witness[str(b)+'/'+scope]=dict(policy=list(map(str,x)),success=str(v),
       silent_unchanged_success=str((1-s)*x[1]),old_union=str(q))
print(json.dumps(dict(direct_history_grid=grids,optimization_bound_checks=boundaries,
    word_queries=word_checks,distinct_later_verdict_profiles=sizes,worked_case=witness),
    sort_keys=True))
