"""Scope-qualified data from a native trace, and sharp finite-law identification."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from hashlib import sha256
import json,sys

PIN='4b7b16966156a6ab78ce10221490d7c16bd16e977c27998dd5acb1ffde53ef49'
def facts(reference):
    b=reference.read_bytes();assert sha256(b).hexdigest()==PIN
    rs=json.loads(b)
    d={(r['arm'],r['lag'],*r['notice_delays']):r for r in rs}
    ret={}
    for k,F,E in product((0,1),repeat=3):
        arms=[d[a,4 if F else None,k,None if F and E else 0] for a in ('discard','retain')]
        # The recovery choice first affects commissioning after the recognized
        # first notice. Earlier physical histories match in its two arms.
        for z in arms:
            assert z['first']==[19,'robot0']
            assert z['notices'][0]==[19+k,'robot0']
            assert not z['reject']
        cut=19+k
        assert [(t,x) for t,x in arms[0]['events'] if t<=cut] == [
            (t,x) for t,x in arms[1]['events'] if t<=cut]
        assert [z['second'] for z in arms]==([[23,'robot1']]*2 if F else [None,None])
        late=[z['finish'] is None or z['finish']>100 for z in arms]
        assert late==[False,bool(F and E)]
        # Under historical discard, production handling has fixed finish time
        # within its context, irrespective of both diagnostic bits.
        assert arms[0]['finish']==93+k
        ret[f'{k}{F}{E}']=[{key:z[key] for key in ('finish','picks_after','moves')} for z in arms]
    return ret

def cell(a,b,x):return (1-a-b+x,b-x,a-x,x)
def extremes(a,b):return max(Q(0),a+b-1),min(a,b)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def bound(lower,upper,total,rate):
    """Each coordinate is probability mass, not a refreshed worst-law draw."""
    y=list(lower);left=total-sum(y)
    assert 0<=left<=sum(upper)-sum(y)
    for i in sorted(range(len(y)),key=lambda i:rate[i],reverse=True):
        take=min(left,upper[i]-y[i]);y[i]+=take;left-=take
    assert not left and sum(y)==total
    return dot(y,rate)

def vertices(lo,hi,total):
    # All but at most one coordinate at a box endpoint.
    for i in range(len(lo)):
        js=[j for j in range(len(lo)) if j!=i]
        for vals in product(*[(lo[j],hi[j]) for j in js]):
            y=[0]*len(lo)
            for j,v in zip(js,vals):y[j]=v
            y[i]=total-sum(vals)
            if lo[i]<=y[i]<=hi[i]:yield y

def plans():
    grid=[Q(i,10) for i in range(11)]
    l=(Q(0),Q(0)); u=(Q(1,4),)*2; z=Q(1,4); cap=Q(1,10)
    criteria=(lambda a:dot(u,a),
              lambda a:bound(l,u,z,a),
              lambda a:dot((0,z),a),
              lambda a:dot((z,0),a))
    results=[]
    for q in criteria:
        v,lams=max((sum(k)/2,k) for k in product(grid,repeat=2) if q(k)<=cap)
        results.append([str(v),list(map(str,lams))])
    assert [v for v,_ in results]==['1/5','2/5','7/10','7/10']
    return results

def verify():
    from random import Random
    rnd=Random(417)
    k_checks=0;vertex_checks=0
    grid=[Q(i,8) for i in range(9)]
    for a,b in product(grid,repeat=2):
        lo,hi=extremes(a,b)
        for x in grid:
            weights=cell(a,b,x)
            assert all(w>=0 for w in weights)==(lo<=x<=hi)
            assert sum(weights)==1 and weights[2]+weights[3]==a and weights[1]+weights[3]==b
            k_checks+=1
    for m in range(1,8):
        for _ in range(90):
            lo=[Q(rnd.randrange(7),31*m) for _ in range(m)]
            hi=[x+Q(rnd.randrange(10),31*m) for x in lo]
            z=sum(lo)+Q(rnd.randrange(19),18)*(sum(hi)-sum(lo))
            rate=[Q(rnd.randrange(11),10) for _ in range(m)]
            vals=[dot(y,rate) for y in vertices(lo,hi,z)]
            assert bound(lo,hi,z,rate)==max(vals)
            assert -bound(lo,hi,z,tuple(-x for x in rate))==min(vals)
            vertex_checks+=1
    h=Q(1,2)
    A=[cell(h,h,x) for x in (0,h)];B=list(reversed(A))
    assert [tuple(sum(c[i] for c in L)/2 for i in range(4)) for L in (A,B)]==[(Q(1,4),)*4]*2
    for d in (0,1):
        assert not set(i for i,w in enumerate(A[d]) if w)&set(i for i,w in enumerate(B[d]) if w)
    return dict(frechet_checks=k_checks,whole_law_lp_queries=2*vertex_checks,
        common_production_policy='guarded discard',
        collection_order=['separate marginals','paired but pooled','linked law A','linked law B'],
        best_retention_fraction_and_policy=plans())

if __name__=='__main__':
    ans=dict(native_controls=facts(Path(sys.argv[1])),bounds=verify())
    out=json.dumps(ans,sort_keys=True,indent=2)+'\n'
    if len(sys.argv)>2:Path(sys.argv[2]).write_text(out)
    else:print(out,end='')
