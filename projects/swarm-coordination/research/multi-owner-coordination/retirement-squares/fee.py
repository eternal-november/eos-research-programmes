"""Check a bounded economic condition separately from physical squares."""
from fractions import Fraction as F
from itertools import product

def cap(v,s,a,l):
    return F(v)-(a-(1-s)*l)/s

def renaming(old,new):
    # There is one common positive affine charge map preserving comparisons
    # to refusal at each attainable interior cap, or no such map.
    x=old[0];y=new[0]
    for u,v in zip(old,new):
        if u!=x:
            A=(v-y)/(u-x);B=y-A*x
            return (A,B) if A>0 and all(i*A+B==j for i,j in zip(old,new)) else None
    return (F(1),y-x) if all(j==y for j in new) else None

def main():
    s=F(1,2)
    a=tuple(cap(18,s,i,0) for i in (0,3,6))
    b=tuple(cap(18,s,i,j) for i,j in ((0,0),(3,3),(6,0)))
    assert a==(18,12,6) and b==(18,15,6)
    assert renaming(a,b) is None and not a[1]>=14 and b[1]>=14
    k=0
    for scalar,offset,x1,x2,y1,y2,p in product((F(1,2),F(1),F(2)),range(-2,3),
                  (F(1,2),F(1)),(F(1,2),F(1)),range(-3,4),range(-3,4),range(1,5)):
        old1=x1*p-y1;old2=x2*p-y2
        p2=scalar*p+offset
        new1=x1*p2-(scalar*y1+offset*x1)
        new2=x2*p2-(scalar*y2+offset*x2)
        assert (new1>=new2)==(old1>=old2)
        k+=1
    print(k,'exact positive affine menu comparison controls; cap triple obstruction',a,b)
if __name__=='__main__':main()
