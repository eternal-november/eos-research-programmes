"""Sequence-form robust controller with a fixed law and actual irreversible work."""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
import json, sys
from scipy.optimize import linprog
ZERO,Q1=Q(0),Q(1)
ROOT=('root',)

def dot(a,b):return sum(x*y for x,y in zip(a,b))
@dataclass
class LP:
    names:list
    bounds:list
    ub:list
    eq:list
    def var(self,name,lo=0,hi=None):
        if name in self.names:raise ValueError(name)
        self.names.append(name);self.bounds.append((lo,hi))
        return len(self.names)-1
    def le(self,row,b):self.ub.append((row,Q(b)))
    def equals(self,row,b):self.eq.append((row,Q(b)))
    def solve(self,obj):
        n=len(self.names)
        dense=lambda r:[r.get(i,0) for i in range(n)]
        c=dense(obj); rows=[dense(r) for r,_ in self.ub];rhs=[b for _,b in self.ub]
        eq=[dense(r) for r,_ in self.eq];req=[b for _,b in self.eq]
        r=linprog([-x for x in c],A_ub=rows or None,b_ub=rhs or None,
                  A_eq=eq or None,b_eq=req or None,bounds=self.bounds,method='highs')
        if r.status==2:return None
        if not r.success:raise RuntimeError(r.message)
        fr=lambda x:Q(float(x)).limit_denominator(10**7)
        x=list(map(fr,r.x))
        assert all(dot(row,x)<=b for row,b in zip(rows,rhs))
        assert all(dot(row,x)==b for row,b in zip(eq,req))
        assert all((l is None or l<=v) and (u is None or v<=u) for v,(l,u) in zip(x,self.bounds))
        yy=[fr(-v) for v in r.ineqlin.marginals]
        zz=[fr(-v) for v in r.eqlin.marginals]
        assert all(y>=0 for y in yy)
        val=dot(rhs,yy)+dot(req,zz)
        for i,(l,u) in enumerate(self.bounds):
            beta=c[i]-sum(row[i]*y for row,y in zip(rows,yy))-sum(row[i]*z for row,z in zip(eq,zz))
            if beta:
                end=u if beta>0 else l
                assert end is not None
                val+=beta*end
        assert val==dot(c,x),(val,dot(c,x))
        return val,x

def hspace(k):
    return tuple(product(range(k),(0,1),(0,1),(0,1)))
def source(k,rectangular=False):
    hs=hspace(k)
    def build(mode0,mode1):
        # mode j chooses whether v mirrors s in that actual s branch.
        return [Q(1,2*k)*(Q(1,4) if u else Q(3,4)) if v==(s^(mode1 if s else mode0)) else ZERO
                for _,s,u,v in hs]
    laws=[build(0,0),build(1,1)]
    if rectangular:laws+=[build(0,1),build(1,0)]
    return hs,laws

def view(h,a):
    k,s,_,v=h
    return (k,s,v if a=='audit' else None)
def options(a):
    return ('stop','go','shield') if a=='early' else ('stop','go')
def scores(h,a,b,prospective):
    _,s,u,v=h
    old = bool(a=='early' and u)
    new = bool(b=='go' and v)
    work = (not old)+int(b!='stop' and not new)+(Q(1,4) if a=='hold' else ZERO)
    return int(old or new),int(new if prospective else old or new),work

def build(hs,forced,prospective):
    lp=LP([],[],[],[]);root=lp.var(ROOT,1,1)
    acts=(forced,) if forced else ('early','hold','audit')
    first={a:lp.var(('first',a),0,1) for a in acts}
    lp.equals({**{j:1 for j in first.values()},root:-1},0)
    for a in acts:
        for obs in sorted(set(view(h,a) for h in hs)):
            ix=[lp.var((a,obs,b),0,1) for b in options(a)]
            lp.equals({**{j:1 for j in ix},first[a]:-1},0)
    indices={name:i for i,name in enumerate(lp.names)}
    coeff=[[{} for _ in hs] for _ in range(3)]
    for j,h in enumerate(hs):
        for a in acts:
            for b in options(a):
                i=indices[a,view(h,a),b]
                for r,v in enumerate(scores(h,a,b,prospective)):
                    if v:coeff[r][j][i]=v
    return lp,coeff,first

def guarantee_endpoints(lp,rows,laws,sign,cap,utility=None):
    for p in laws:
        r={}
        for law,vals in zip(p,rows):
            for i,v in vals.items():r[i]=r.get(i,0)+sign*law*v
        if utility is not None:r[utility]=1
        lp.le(r,cap)

def compress_segment(laws):
    A,B=laws;l=[min(a,b) for a,b in zip(A,B)];u=[max(a,b) for a,b in zip(A,B)]
    delta=[a-b for a,b in zip(A,B)];j=next(i for i,d in enumerate(delta) if d)
    H=[]
    for i,di in enumerate(delta):
        if i==j:continue
        r=[0]*len(B);r[i]=delta[j];r[j]=-di;H.append(r)
    z=[dot(r,[b-a for a,b in zip(l,B)]) for r in H]
    return l,[b-a for a,b in zip(l,u)],H,z

def guarantee_pooled(lp,rows,laws,sign,cap,utility=None):
    l,c,H,d=compress_segment(laws)
    stamp=len(lp.names)
    e=[lp.var(('price',stamp,i),None,None) for i in range(len(H))]
    s=[lp.var(('slack',stamp,i)) for i in range(len(l))]
    final={**dict(zip(e,d)),**dict(zip(s,c))}
    for j,row in enumerate(rows):
        v={i:sign*y for i,y in row.items()}
        lp.le({**v,s[j]:-1,**{i:-r[j] for i,r in zip(e,H) if r[j]}},0)
        for i,y in v.items():final[i]=final.get(i,0)+l[j]*y
    if utility is not None:final[utility]=1
    lp.le(final,cap)

def realize(k,forced,tight,prospective,rectangular=False,pooled=False):
    hs,laws=source(k,rectangular)
    lp,coeff,first=build(hs,forced,prospective)
    u=lp.var(('guaranteed_work',),0,3)
    add=guarantee_pooled if pooled else guarantee_endpoints
    add(lp,coeff[0],laws,1,Q(1,4))
    if tight:add(lp,coeff[1],laws,1,Q(1,8))
    add(lp,coeff[2],laws,-1,0,u)
    found=lp.solve({u:1})
    if found is None:return None
    val,x=found
    pairs={}
    for r,rows in enumerate(coeff):
        ys=[sum(x[i]*a for i,a in row.items()) for row in rows]
        pairs[r]=[dot(law,ys) for law in laws]
    assert max(pairs[0])<=Q(1,4) and min(pairs[2])==val
    if tight:assert max(pairs[1])<=Q(1,8)
    # The feasible vector determines a local behavioral controller by the
    # conditional rate of an action on its own realized prefix.
    return val,[(a,x[i]) for a,i in first.items()],len(lp.names),len(lp.eq)

def exhaustive(k,forced,tight,prospective,rectangular):
    hs,laws=source(k,rectangular)
    lp=LP([],[],[],[]); effects=[[{} for _ in hs] for _ in range(3)]
    for a in ((forced,) if forced else ('early','hold','audit')):
        cells=sorted(set(view(h,a) for h in hs))
        for actions in product(options(a),repeat=len(cells)):
            v=lp.var((a,actions),0,1)
            by_obs=dict(zip(cells,actions))
            for i,h in enumerate(hs):
                for r,z in enumerate(scores(h,a,by_obs[view(h,a)],prospective)):
                    if z:effects[r][i][v]=z
    lp.equals({i:1 for i in range(len(lp.names))},1)
    util=lp.var(('minimum_work',),0,3)
    guarantee_endpoints(lp,effects[0],laws,1,Q(1,4))
    if tight:guarantee_endpoints(lp,effects[1],laws,1,Q(1,8))
    guarantee_endpoints(lp,effects[2],laws,-1,0,util)
    answer=lp.solve({util:1})
    return answer[0] if answer else None

def verify():
    names=[
      ('original',None,False,False,False),('timely_binding',None,True,False,False),
      ('timely_no_old_exemption',None,True,False,False),('late_binding','early',True,False,False),
      ('late_exemption','early',True,True,False),('late_hold','hold',True,False,False),
      ('late_hold_resampled','hold',True,False,True)]
    out={}
    for name,a,b,c,d in names:
        r=realize(1,a,b,c,d)
        v=r[0] if r else None
        assert v==exhaustive(1,a,b,c,d)
        if not d:
            p=realize(1,a,b,c,d,pooled=True)
            assert v==(p[0] if p else None)
        out[name]=None if v is None else str(v)
    expect={'original':'7/4','timely_binding':'13/8','timely_no_old_exemption':'13/8',
            'late_binding':None,'late_exemption':'7/4','late_hold':'11/8','late_hold_resampled':'5/4'}
    assert out==expect,(out,expect)
    runs=[]
    for k in (2,4,8,16):
        # Replicate independently distributed readout labels; no value gain,
        # but raw pure-policy instructions would be exponentially numerous.
        r=realize(k,None,True,False,pooled=True)
        assert r[0]==Q(13,8)
        runs.append(dict(labels=k,variables=r[2],information_flows=r[3],guaranteed=str(r[0])))
    return dict(model_values=out,pooled_scaling=runs)
if __name__=='__main__':
    out=json.dumps(verify(),sort_keys=True,indent=2)+'\n'
    if len(sys.argv)>1:open(sys.argv[1],'w').write(out)
    else:print(out,end='')
