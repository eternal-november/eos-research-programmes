from itertools import product

def assess(C,a,b,x,h,t,scope):
    s,r=scope
    # Strict rolling window; initial debit at time 0 remains through 1.
    # h is before 1 and simultaneous sends at h have old precedence.
    initial=a if t<=1 else 0
    if t<h:
        new=initial+x<=C
        old=b+a+(x if new and (s or r) else 0)<=C
    else:
        old=a+b<=C if s or r else b<=C
        still_old=t<=h+1
        new=x+initial+(b if still_old and (s or r) and old else 0)<=C
    return old,new

def choose(C,a,b,x,h,options,admitted):
    if not admitted:return None
    return next((t for t in options if all(all(assess(C,a,b,x,h,t,m)) for m in admitted)),None)
