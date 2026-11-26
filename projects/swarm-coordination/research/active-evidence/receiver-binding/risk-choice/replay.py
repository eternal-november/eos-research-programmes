"""Robust decisions over complete native effect types, not empirical weights."""
from fractions import Fraction as F
from itertools import product,combinations
import subprocess,sys,json

actual={}
parameters=[]
for z,probe,shared,drop in product((2,3),(0,1),(0,1),(0,1)):
    parameters.append((5,2,2,probe,2,z,0,shared,drop))
cmd=''.join(' '.join(map(str,x))+'\n' for x in parameters)
r=subprocess.run([sys.argv[1]],input=cmd,text=True,capture_output=True,check=True)
for tup, line in zip(parameters,r.stdout.splitlines(),strict=True):
    a=tuple(map(int,line.split()));assert len(a)==6
    _,_,_,probe,_,z,_,shared,drop=tup
    seen,old,nxt,*_=a
    assert old==1
    ref_seen=probe and not shared and not drop
    assert seen==ref_seen
    assert nxt==(2+z +(2 if shared else 1 if ref_seen else 0)<=5)
    actual[z,probe,shared,drop]=a[:3]

class Polyhedron:
    def __init__(self):
        self.d={}
    def add(self,row,bound):
        row=tuple(map(F,row));bound=F(bound)
        if any(row):self.d[row]=min(self.d.get(row,bound),bound)
        else:assert bound>=0
    def opt(self,priority):
        score=None
        constraints=tuple(self.d.items())
        for eqs in combinations(constraints,5):
            aug=[list(row)+[b] for row,b in eqs]
            for j in range(5):
                pivot=next((k for k in range(j,5) if aug[k][j]),None)
                if pivot is None:break
                aug[pivot],aug[j]=aug[j],aug[pivot]
                a=aug[j][j]
                for k in range(j,6):aug[j][k]/=a
                for i in range(5):
                    if i==j:continue
                    z=aug[i][j]
                    if z:
                        for k in range(j,6):aug[i][k]-=z*aug[j][k]
            else:
                x=[r[-1] for r in aug]
                if all(sum(a*b for a,b in zip(row,x))<=t for row,t in constraints):
                    key=(sum(a*b for a,b in zip(priority,x)),-x[0])
                    if score is None or key>score:
                        score=key
        assert score is not None
        return score

def direct(z,s,d,e,k,conditional):
    L,U=max(0,1-s-d),min(1-s,1-d)
    # l, n, a, b, t: probe choice, three unconditional decision
    # weights of the stage-two randomized policy, and worst good service.
    p=Polyhedron()
    for i in range(5):p.add(tuple(-int(k==i) for k in range(5)),0)
    p.add((1,0,0,0,0),1)
    p.add((1,1,0,0,0),1)
    p.add((-1,0,1,0,0),0)
    p.add((-1,0,0,1,0),0)
    for rho in {L,U}:
        # Four atoms; each joint law is fixed, with the declared marginals.
        ds=1-s-rho
        atoms={(0,0):rho,(0,1):ds,(1,0):1-d-rho,(1,1):d-ds}
        assert min(atoms.values())>=0 and sum(atoms.values())==1
        risks=[F(0)]*3
        good=[F(0)]*3
        for (shared,drop),w in atoms.items():
            _,_,nxt=actual[z,0,shared,drop]
            good[0]+=w*nxt;risks[0]+=w*(1-nxt)
            seen,_,nxt=actual[z,1,shared,drop]
            j=1 if seen else 2
            good[j]+=w*nxt;risks[j]+=w*(1-nxt)
        if conditional:
            p.add((e,risks[0],0,0,0),e)
            p.add((-e*rho,0,risks[1],0,0),0)
            p.add((-e*(1-rho),0,0,risks[2],0),0)
        else:p.add((0,*risks,0),e)
        p.add((0,*(-g for g in good),1),0)
    return p.opt((-k,0,0,0,1))

def closed(z,s,d,e,k,conditional):
    L,U=max(0,1-s-d),min(1-s,1-d)
    x=min(1,e/s) if s else F(1)
    G=(1-s)*x
    if z==3 or s in (0,1) or x==1:return G,0
    if not conditional:
        if L<=k:return G,0
        return G+(L-k)*(1-x),-(1-x)
    y=min(1,e*(1-U)/s)
    h=L+(1-s-L)*y-k
    return (h,-1) if h>G else (G,0)

cases=0
for s,d,e,k in product(map(F,('0','1/4','1/2','1')),
                       map(F,('0','1/4','3/4')),
                       map(F,('0','1/8','1/2')),
                       map(F,('0','1/8','7/8'))):
    # All edge cases stay; sample some interior workloads.
    if s not in (0,1) and d not in (0,) and k==F(7,8) and e!=0:continue
    for z,conditional in product((2,3),(False,True)):
        a=closed(z,s,d,e,k,conditional)
        b=direct(z,s,d,e,k,conditional)
        assert a==b,(z,s,d,e,k,conditional,a,b)
        cases+=1

example={}
for z,c in product((2,3),(False,True)):
    args=(z,F(1,5),F(1,5),F(1,10),F(1,20),c)
    a=closed(*args);b=direct(*args);assert a==b
    example[f'z{z}-conditional{c}']=dict(objective=str(a[0]),probe_fraction=str(-a[1]))
print(json.dumps(dict(native_cases=len(actual),exact_policy_cases=cases,example=example),
                 indent=2,sort_keys=True))
