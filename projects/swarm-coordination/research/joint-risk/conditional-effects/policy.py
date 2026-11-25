"""Pre-cut layout choice, actual retained harm, and deterministic local continuation."""
from fractions import Fraction as F
from itertools import product
from coupled import Row,trace,joint,exact,cut,union

H=('green','amber')
PLANS={'green':(None,2,3),'amber':(None,5,6)}
LOCAL={'green':F(1,2),'amber':F(4,5)}
GLOBAL=F(3,5)

def rules():
    for config in ('green-fast','amber-fast'):
        for p in product(*(PLANS[h] for h in H)):
            yield (config,dict(zip(H,p)))

def source(config,policy,n):
    # Execute one installed layout, then one fixed action per actual report.
    # No latent-mode table lookup by the controller.
    phases=trace(config,None,n)
    return [r._replace(future=int(r.phase==policy[r.report])) for r in phases]

def vector(rows,n,interest,observed=None):
    return tuple(F(sum(interest(r) and (observed is None or observed==r.report)
                       for r in rows if r.label==i),8) for i in range(n))

def worst(v,w):
    return (1-w)*sum(v)/len(v)+w*max(v)

def compiled(config,p,n,w):
    rows=source(config,p,n)
    # Verified report condition may tighten cap on ALL harm, not just new actions.
    for h in H:
        if not cut(*joint(rows,h,union,n),w,LOCAL[h]):return None
    if worst(vector(rows,n,union),w)>GLOBAL:return None
    good=vector(rows,n,lambda r:p[r.report] is not None and not union(r))
    return -worst(tuple(-x for x in good),w)

def full_trace_assembly(config,p,n,w):
    rows=source(config,p,n);a=(1-w)/n
    values=[]
    # Same index j retained across each report and action, never resampled.
    for j in range(n):
        def mass(r):return (a+w*int(r.label==j))/8
        event_total=sum(mass(r) for r in rows if union(r))
        if event_total>GLOBAL:return None
        for h in H:
            group=[r for r in rows if r.report==h]
            if sum(mass(r) for r in group if union(r))>LOCAL[h]*sum(mass(r) for r in group):return None
        values.append(sum(mass(r) for r in rows if p[r.report] is not None and not union(r)))
    return min(values)

def stickiness():
    # The report is independent of latent label but not of what risks the
    # actual downstream action runs. The same law applies in both leaves.
    n=2;w=F(3,5)
    rows=[Row(i,p,H[p//4],0,0,int(i==p//4)) for i,p in product(range(n),range(8))]
    combined=worst(vector(rows,n,union),w)
    separately=[exact(*joint(rows,h,union,n),w) for h in H]
    assert combined==F(1,2) and separately==[F(4,5),F(4,5)]
    print('single fixed source law: mission cap 1/2 passes, per-report cap 1/2 fails')

def main():
    count=0
    for n,w in product(range(2,13),(F(0),F(1,4),F(1,2),F(3,4))):
        all_scores=[]
        for config,p in rules():
            a=compiled(config,p,n,w);b=full_trace_assembly(config,p,n,w)
            assert a==b
            if a is not None:all_scores.append((config,a,p))
            count+=1
        assert all(x[0]=='green-fast' for x in all_scores)
        # Even rejecting all new work cannot recover the bad layout under
        # the active cap, because the old valve reached its effect earlier.
        assert compiled('amber-fast',{h:None for h in H},n,w) is None
    result=[
        (compiled(c,p,4,F(1,4)),p) for c,p in rules() if compiled(c,p,4,F(1,4)) is not None]
    print(count,'joint policy choices compared to exact same-law physical trace assembly')
    print('best useful completion probability in the example:',max(x[0] for x in result))
    stickiness()
if __name__=='__main__':main()
