"""Two-disc identity ambiguity across a totally unobserved interval."""
from itertools import product
from collections import defaultdict
from heapq import heappop,heappush
from math import hypot,sin,cos,acos,pi,sqrt
import json

def route(r,d,a):
    a=abs(a)
    assert 0<=a<=pi and r>=d>0
    tangent=acos(d/r)
    if a<=2*tangent:
        return 2*r*sin(a/2)
    return 2*sqrt(r*r-d*d)+d*(a-2*tangent)

def assignments(r,d,V,a,T):
    return tuple(i for i,g in enumerate((a,pi-a)) if route(r,d,g)<=2*V*T)

def polygon(n,d,circumscribed):
    r=d/cos(pi/n) if circumscribed else d
    verts=[(r*cos(2*pi*j/n),r*sin(2*pi*j/n)) for j in range(n)]
    bounds=[(cos(2*pi*(j+.5)/n),sin(2*pi*(j+.5)/n),
             d if circumscribed else d*cos(pi/n)) for j in range(n)]
    return verts,bounds

def can_see(p,q,bounds):
    # Intersection of the parameterized segment with strict inside all
    # convex polygon halfplanes. Model eval has explicit numerical margin.
    lo,hi=0.,1.
    for nx,ny,b in bounds:
        z=nx*p[0]+ny*p[1]-b+1e-11
        a=nx*(q[0]-p[0])+ny*(q[1]-p[1])
        if abs(a)<1e-13:
            if z>=0:return True
            continue
        if a>0:hi=min(hi,-z/a)
        else:lo=max(lo,-z/a)
        if lo>=hi:return True
    return not lo<hi

def polygon_dijkstra(radius,clearance,angle,n,outside):
    verts,bounds=polygon(n,clearance,outside)
    p=(radius,0.)
    q=(radius*cos(angle),radius*sin(angle))
    points=verts+[p,q]
    ng=defaultdict(list)
    def add(i,j):
        x,y=points[i]
        a,b=points[j]
        w=hypot(x-a,y-b)
        ng[i].append((j,w))
        ng[j].append((i,w))
    for j in range(n):
        add(j,(j+1)%n)
        for i in (n,n+1):
            if can_see(points[i],points[j],bounds):add(i,j)
    if can_see(p,q,bounds):add(n,n+1)
    best={n:0.}
    heap=[(0.,n)]
    while heap:
        d,k=heappop(heap)
        if d>best[k]:continue
        if k==n+1:return d
        for i,w in ng[k]:
            if d+w<best.get(i,float('inf')):
                best[i]=d+w
                heappush(heap,(d+w,i))
    raise AssertionError("unreachable between valid endpoints")

def parity(s0,transport):
    # The latest authenticated named end anchors one permutation, if
    # physically authorized to answer the target identity question.
    s=set(s0)
    for u in transport:s={x^y for x,y in product(s,u)}
    return s

def main():
    rows=0
    max_width=0.
    for radius,angle,n in product((1.05,1.25,1.5,2.,3.),(0.,.4,1.1,1.9,2.4,2.8,pi),(24,48,96)):
        actual=route(radius,1.,angle)
        low=polygon_dijkstra(radius,1.,angle,n,False)
        high=polygon_dijkstra(radius,1.,angle,n,True)
        assert low-2e-9<=actual<=high+2e-9,(radius,angle,n,low,actual,high)
        max_width=max(max_width,high-low);rows+=1
    assert assignments(1,.5,1,0,1.08)==(0,)
    assert assignments(1,.5,1,0,1.20)==(0,1)
    swap=route(1,.5,pi)/2
    assert 1.08<swap<1.20
    # Construct a shared trace at the identical anonymous observation:
    # start and end on the diameter antipodes, tangent + arc + tangent.
    r,d,V=1.,.5,1.
    a=acos(d/r)
    p0=(r,0.)
    c0=(d*cos(a),d*sin(a))
    c1=(d*cos(pi-a),d*sin(pi-a))
    p1=(-r,0.)
    seg=lambda p,q,t:tuple((1-t)*x+t*y for x,y in zip(p,q))
    nodes=[seg(p0,c0,z/100) for z in range(101)]
    nodes += [(d*cos(a+(pi-2*a)*j/100),d*sin(a+(pi-2*a)*j/100))
              for j in range(1,101)]
    nodes += [seg(c1,p1,z/100) for z in range(1,101)]
    assert all(d-1e-12<=hypot(*p)<=r+1e-12 for p in nodes)
    obs=lambda p: sorted([(p[0]/2,p[1]/2),(-p[0]/2,-p[1]/2)])
    assert obs(nodes[0])==obs(nodes[-1])
    # Initial naming is known. Anonymous windows do not repair a previously
    # lost label just by forcing identity in the newest local transfer.
    tests=0
    for seq in product(((0,),(1,),(0,1)),repeat=7):
        opts=parity({0},seq)
        exhaustive={sum(z)%2 for z in product(*seq)}
        assert opts==exhaustive and (len(opts)==2)==((0,1) in seq)
        tests+=1
    assert parity({0},[(0,1),(0,)])=={0,1}
    assert parity({1},[(0,)])=={1}  # post-confusion named anchor
    print(json.dumps(dict(numerical_bound_controls=rows,maximum_bracket_width=round(max_width,8),
       constructed_swap_samples=len(nodes),traces=tests,swap_time_same_anonymous_view=round(swap,9),
       pairwise_independent_threshold=1,at_1_08=['same'],at_1_20=['same','swap'],
       fresh_anonymous_frames_do_not_restore_name=True),indent=2,sort_keys=True))
if __name__=='__main__':main()
