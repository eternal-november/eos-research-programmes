from itertools import combinations,product

def side_rendezvous(local,stop,g,r,T):
    # Coordinates increase from this side's anchor toward the stopped body.
    # No position from the opposite side is an input.
    a=b=local[0]; saved=[(a,b)]
    if r<g or a>stop-g:return None
    for x in local[1:]:
        a=max(local[0],x-T,a+g)
        b=min(stop-g,x+T,b+r)
        if a>b:return None
        saved.append((a,b))
    p=[b]
    for lo,hi in reversed(saved[:-1]):
        p.append(max(lo,p[-1]-r))
        assert p[-1]<=min(hi,p[-2]-g)
    return tuple(reversed(p))

def full_reference(xs,f,g,r,T):
    choices=[]
    for i,x in enumerate(xs):
        if i in [0,len(xs)-1]: choices.append((x,));continue
        choices.append(tuple(y for y in range(x-T,x+T+1)
                             if y<=f-g if x<f)
                       if x<f else tuple(y for y in range(x-T,x+T+1) if y>=f+g))
    return any(all(g<=b-a<=r for a,b in zip(ys,ys[1:]))
               for ys in product(*choices))

n=0
for L,count,g,r,T in product(range(5,11),range(2,6),range(1,3),range(1,6),range(4)):
    for interior in combinations(range(1,L),count):
        allx=(0,*interior,L)
        if any(b-a<g for a,b in zip(allx,allx[1:])):continue
        for f in interior:
            xs=tuple(i for i in allx if i!=f)
            left=side_rendezvous(tuple(x for x in xs if x<f),f,g,r,T)
            right=side_rendezvous(tuple(-x for x in reversed(xs) if x>f),-f,g,r,T)
            local=left is not None and right is not None and -right[-1]-left[-1]<=r
            assert local==full_reference(xs,f,g,r,T)
            if local:
                merged=left+tuple(-x for x in reversed(right))
                assert all(abs(x-y)<=T for x,y in zip(xs,merged))
                assert all(g<=b-a<=r for a,b in zip(merged,merged[1:]))
                assert all(y<=f-g if x<f else y>=f+g for x,y in zip(xs,merged))
            n+=1
print(n,"split-controller replays agree with a whole-configuration oracle")
print("left near-edge plan", side_rendezvous((0,2),4,1,3,1))
print("right near-edge plan",side_rendezvous((-9,-7),-4,1,3,1))
