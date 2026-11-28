"""Physical penultimate chord, bounded sensor, and native dispatch pose."""
from fractions import Fraction as F
from math import isqrt
from itertools import pairwise,product
from pathlib import Path
import ast,json,sys
paths,portals,ride,out,sites=map(Path,sys.argv[1:])
solved=json.loads(paths.read_text())
brackets=[json.loads(l) for l in portals.read_text().splitlines()]
def slab_spec():
    tree=ast.parse(ride.read_text())
    s=next(a.value for a in tree.body if isinstance(a,ast.Assign) and [t.id for t in a.targets if isinstance(t,ast.Name)]==["closures"])
    return {ast.literal_eval(k):tuple(tuple(F(ast.literal_eval(a.args[0])) for a in e.elts)
                                     for e in j.elts)
            for k,j in zip(s.keys,s.values)}
slabs=slab_spec()
cases=[]
for gate,code,slab,idx in ((0,'A',slabs[117,132],4),(1,'B',slabs[118,132],5)):
    p=solved[code]['polyline']
    full=p+p[-2::-1]
    i=2*(len(p)-1)-1-idx
    src,dst=full[i:i+2]
    assert src==p[idx+1] and dst==p[idx]
    L=lambda a,b:sum((x-y)**2 for x,y in zip(a,b))
    dur=lambda n:isqrt(n*10**12)+int(isqrt(n*10**12)**2!=n*10**12)+200000
    start=1_000_000+sum(dur(L(a,b)) for a,b in pairwise(full[:i+1]))
    n=L(src,dst); end=start+dur(n)
    gain=10**14
    floor=isqrt(n*gain*gain)
    lo,hi=F(floor,gain),F(floor+1,gain)
    axis=min(range(3),key=lambda i: slab[1][i]-slab[0][i])
    sign=1 if dst[axis]>src[axis] else -1
    plane=slab[sign==1][axis]
    pad=F(302,1000)
    assert end<=brackets[gate]['end']
    h=brackets[gate]['hulls'][1][1]
    core=brackets[gate]['cores'][1]
    if sign>0:assert src[axis]<plane<dst[axis]
    else:assert dst[axis]<plane<src[axis]
    def xyz(t):
        meters=F(t-start-100000,10**6)
        assert 0<=meters<=lo-F(1,10)
        return [tuple(sorted((s+(d-s)*meters/lo,s+(d-s)*meters/hi))) for s,d in zip(src,dst)]
    def nearest(pair):
        a,b=pair
        k=(a+F(1,2)).numerator//(a+F(1,2)).denominator
        assert k-F(1,2)<a<=b<k+F(1,2)
        return k
    T=h+65000
    clear=sorted(sign*(x-plane)-pad for x in xyz(T)[axis])
    maximum=int(clear[0]*500000)
    assert F(2*maximum,10**6)<clear[0]<=clear[1]<F(2*(maximum+1),10**6)
    for mode,error,bias,latency in (('point',0,0,10000),('exact',0,0,10000),
                ('bounded',10000,-10000,10000),('bounded-positive',10000,10000,10000),
                ('poor',40000,-40000,10000),('late',0,0,100000),
                ('last-error',maximum,-maximum,10000),('over-error',maximum+1,-maximum-1,10000)):
        margin=F(error,10**6)+(0 if mode=='point' else pad)
        beta=F(bias,10**6)
        assert abs(beta)<=F(error,10**6)
        def score(t):
            return sorted(sign*(x-plane)+beta-margin for x in xyz(t)[axis])
        l=start+100001; r=end-200002
        while l<r:
            m=(l+r)//2
            if score(m)[0]>0:r=m
            else:l=m+1
        assert score(l)[0]>0 and score(l-1)[1]<=0
        receive=l+latency
        if mode=='point':assert core[0]<receive<core[1]
        else:assert h<receive
        between=(brackets[gate]['hulls'][0][1]+1000000, l, receive)
        assert between[0]<l<receive<end
        glyph=mode!='point'
        body_exit_bracket=[str(x) for x in xyz(l)[axis]]
        cases.append(dict(gate=gate,act=receive,witness=l,h=h,latency=latency,slot=between[0],body=glyph,
             maximum_error_um=maximum,body_pose=body_exit_bracket,
             witness_xyz=[[str(a),str(b)] for a,b in xyz(l)],
             velocity_xyz=[[str(x) for x in sorted(((d-s)/lo,(d-s)/hi))] for s,d in zip(src,dst)],coord=[nearest(t) for t in xyz(receive)],
             at=idx,error=error,bias=bias,axis=axis,plane=str(plane),sign=sign,mode=mode))
out.write_text(json.dumps(cases,sort_keys=True)+"\n")
sites.write_text(json.dumps(sorted(set(tuple(x['coord']) for x in cases)))+"\n")
