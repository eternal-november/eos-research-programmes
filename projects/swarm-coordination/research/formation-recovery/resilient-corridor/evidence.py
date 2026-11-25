"""Same-cut anchor observations for robust two-hop report transfer."""
from itertools import product
from deadline import oracle

def anchors(x,R):
    audible_L=[i for i in range(1,len(x)-1) if x[i]-x[0]<=R]
    audible_R=[i for i in range(1,len(x)-1) if x[-1]-x[i]<=R]
    return max(audible_L,default=0),min(audible_R,default=len(x)-1)

if __name__=="__main__":
    n=0
    for count in range(3,8):
        for gaps in product(range(1,4),repeat=count-1):
            x=[0]
            for d in gaps:x.append(x[-1]+d)
            for R,k in product(range(1,6),range(min(count-1,4))):
                p,q=anchors(x,R)
                exact=(x[-1]-x[0]<=R or max(0,p-q+1)>k)
                assert exact==(oracle(x,R,k)<=2)
                n+=1
    print(n,"same-cut anchor-rank comparisons to physical-link/deletion BFS")
    left_before=anchors((0,4,11),6)[0]
    right_after=anchors((0,7,11),6)[1]
    assert left_before==right_after==1
    assert oracle((0,7,11),6,0)>2
    print("individually truthful pre/post rank reports falsely certify the current graph without the shared effect cut")
