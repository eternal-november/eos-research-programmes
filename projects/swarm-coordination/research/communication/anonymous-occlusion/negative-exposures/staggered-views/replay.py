"""Exact rational no-object inference from qualified asynchronous views."""
from dataclasses import dataclass,replace
from fractions import Fraction as Q
from itertools import product
import json

@dataclass(frozen=True)
class I:
    l:Q
    r:Q
    lc:bool=True
    rc:bool=True

    def live(self):
        return self.l<self.r or (self.l==self.r and self.lc and self.rc)

    def has(self,x):
        return (self.l<x or (self.l==x and self.lc)) and (x<self.r or (x==self.r and self.rc))

def cap(a,b):
    l,r=max(a.l,b.l),min(a.r,b.r)
    out=I(l,r,a.has(l) and b.has(l),a.has(r) and b.has(r))
    return out if out.live() else None

def minus(a,b):
    p=cap(a,b)
    if p is None:return (a,)
    ans=(I(a.l,p.l,a.lc,a.has(p.l) and not b.has(p.l)),
         I(p.r,a.r,a.has(p.r) and not b.has(p.r),a.rc))
    return tuple(q for q in ans if q.live())

@dataclass(frozen=True)
class Frame:
    capture:Q
    arrival:Q
    view:I
    warranted:bool=True

def available(frames,now):
    return tuple(f for f in frames if f.warranted and f.capture<=f.arrival<=now)

def strip_erosion(domain,tau,speed,frames):
    supply=(domain,)
    for f in frames:
        q=speed*abs(tau-f.capture)
        region=I(f.view.l+q,f.view.r-q,f.view.lc,f.view.rc)
        if region.live():supply=tuple(y for x in supply for y in minus(x,region))
    return supply

def reachable(domain,tau,speed,frames):
    def direction(s):
        ordered=sorted(((f.capture*s,f.view) for f in frames if s*f.capture<=s*tau),
                       key=lambda p:p[0])
        out=(domain,)
        t=ordered[0][0] if ordered else s*tau
        def move(a,b):
            r=speed*(b-a)
            return tuple(x for p in out
                if (x:=cap(I(p.l-r,p.r+r,p.lc,p.rc),domain)) is not None)
        for when,neg in ordered:
            out=tuple(q for p in move(t,when) for q in minus(p,neg))
            t=when
        return move(t,s*tau)
    return tuple(z for a,b in product(direction(1),direction(-1))
                 if (z:=cap(a,b)) is not None)

def direct_possible(domain,tau,speed,frames,query):
    # Enumerate both sides of every closed negative. Strict difference
    # constraints handle open endpoints without discretizing the state.
    # f: actual capture, unused arrival, qualified view (closed here).
    assert all(f.view.lc and f.view.rc for f in frames)
    times=sorted({tau}|{f.capture for f in frames})
    ix={t:i+1 for i,t in enumerate(times)}
    N=len(times)+1
    for bits in product((0,1),repeat=len(frames)):
        dist=[[(0,0) if i==j else None for j in range(N)] for i in range(N)]
        def put(a,b,k,s=False):
            z=(k,-int(s))  # x_b - x_a <= (k,strict)
            if dist[a][b] is None or z<dist[a][b]:dist[a][b]=z
        def apply(i,x):
            put(0,i,x.r,not x.rc)
            put(i,0,-x.l,not x.lc)
        for t in times:apply(ix[t],domain)
        apply(ix[tau],query)
        for a,b in zip(times,times[1:]):
            dt=speed*(b-a)
            put(ix[a],ix[b],dt)
            put(ix[b],ix[a],dt)
        for f,b in zip(frames,bits):
            if b:put(ix[f.capture],0,-f.view.r,True)
            else:put(0,ix[f.capture],f.view.l,True)
        for k in range(N):
            for i,j in product(range(N),repeat=2):
                a,b=dist[i][k],dist[k][j]
                if a is not None and b is not None:
                    z=(a[0]+b[0],min(a[1],b[1]))
                    if dist[i][j] is None or z<dist[i][j]:dist[i][j]=z
        if all(dist[k][k]>=(0,0) for k in range(N)):return True
    return False

def verdict(pos,target):
    if not pos:return 'inconsistent'
    return 'possible' if any(cap(x,target) is not None for x in pos) else 'empty'

def frame(t,l,r,arrival=4,valid=True):return Frame(t,arrival,I(l,r),valid)

def main():
    D=I(-8,8)
    examples=[]
    widths=(Q(1,2),1,Q(3,2),2,3)
    for V,delta,overlap in product((Q(1,2),1,2),(Q(1,2),1,Q(3,2)),widths):
        B=I(-2,2)
        h=Q(overlap)
        z=(frame(-delta,-6,h/2),frame(delta,-h/2,6))
        if V*delta<=Q(3):
            simple=verdict(strip_erosion(D,0,V,z),B)
            exact=verdict(reachable(D,0,V,z),B)
            expect='empty' if h>=2*V*delta else 'possible'
            assert simple==exact==expect, (V,delta,h,simple,exact)
            if expect=='possible':
                # Speed-V linear witness lies outside both given half-views.
                assert V*delta>h/2 and -V*delta< -h/2
            examples.append(expect)
    # Strong direct propagation finds an exclusion no single slab can prove.
    z=(frame(0,-1,2),frame(1,-1,Q(1,2)))
    point=I(0,0)
    strict=[verdict(g(D,2,1,z),point) for g in (strip_erosion,reachable)]
    assert strict==['possible','empty']
    assert not direct_possible(D,2,1,z,point)
    # Both cameras tie to a single uncertain offset relative to quantity
    # probed; compare individual worst-case eroding versus joined worlds.
    a,b=frame(-1,-6,1,2),frame(1,-1,6,3)
    j=Q(1,2)
    common=tuple([replace(a,capture=a.capture+h),replace(b,capture=b.capture+h)]
                 for h in (-j,j))
    independent=tuple([replace(a,capture=a.capture+h),replace(b,capture=b.capture+k)]
                      for h,k in product((-j,j),repeat=2))
    B=I(-1,1)
    def law(worlds,now):
        return [verdict(reachable(D,0,1,available(z,now)),B) for z in worlds]
    assert law(common,3)==['empty','empty']
    assert 'possible' in law(independent,3)
    assert law(common,2)==['possible','possible']
    naive=(replace(a,capture=-Q(3,2)),replace(b,capture=Q(3,2)))
    assert verdict(strip_erosion(D,0,1,naive),B)=='possible'
    assert verdict(reachable(D,0,1,(frame(0,-8,8),)),B)=='inconsistent'
    # Exact rational cross-check against an independent strict linear
    # constraint feasibility method for arbitrary binary left/right cases.
    bounds=(I(-4,-1),I(-1,2),I(0,0),I(1,5),I(-8,8))
    count=0
    for records,tau,speed,q in product(product(bounds,repeat=3),(-1,0,1,2,3),
                  (Q(1,2),1,2),(I(-3,-2),I(0,0),I(4,6))):
        z=tuple(Frame(t,4,x) for t,x in enumerate(records))
        pos=reachable(D,tau,speed,z)
        assert (verdict(pos,q)=='possible')==direct_possible(D,tau,speed,z,q),(z,tau,speed,q)
        count+=1
    # A held-in passive raster: reflectance blob (no identity code) appears
    # iff qualifying aperture physically includes its projected center.
    def raster(z,p):
        assert 4*p==int(4*p)
        return bytes(255 if q==4*p and z.has(Q(q,4)) else 0
                     for q in range(-32,33))
    early,late=Q(-1,2),Q(1,2)
    narrow=(I(-6,Q(1,4)),I(-Q(1,4),6))
    wide=(I(-6,Q(1,2)),I(-Q(1,2),6))
    negative=bytes(65)
    swapline=(Q(1,2),-Q(1,2))
    assert all(raster(z,7)==negative for z in narrow+wide)
    assert [raster(z,p)==negative for z,p in zip(narrow,swapline)]==[True,True]
    assert [raster(z,p)==negative for z,p in zip(wide,swapline)]==[False,False]
    # Historical separator can serve as the missing middle cut from #613
    # when both frames arrive by the later authority decision.
    zz=tuple(Frame(t,a,w) for t,a,w in zip((early,late),(-Q(1,4),Q(3,4)),wide))
    band=I(-Q(3,5),Q(3,5))
    assert verdict(reachable(D,0,1,available(zz,1)),band)=='empty'
    deferred=(zz[0],replace(zz[1],arrival=Q(5,4)))
    assert verdict(reachable(D,0,1,available(deferred,1)),band)=='possible'
    assert verdict(reachable(D,0,1,available(deferred,Q(5,4))),band)=='empty'
    assert Q(1)<=2*Q(3,5)<2
    print(json.dumps(dict(overlap_cases=len(examples),exact_direct_comparisons=count,
        marginal_erosion_vs_exact=strict,clock_common_after_all=law(common,3),
        clock_independent_after_all=law(independent,3),
        same_clock_before_last_delivery=law(common,2),
        middle_certificate_can_close_original_gap=True,
        late_frame_cannot_authorize_at_cut=True,
        raster_equal_payloads_if_insufficient_overlap=True,
        naive_individual_erosion='possible',empty_support_rejected=True),indent=2,sort_keys=True))
if __name__=='__main__':main()
