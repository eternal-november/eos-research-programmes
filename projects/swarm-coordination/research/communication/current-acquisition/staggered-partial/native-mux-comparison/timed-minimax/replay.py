from fractions import Fraction as F
import json
from scan import opt
from lp_check import verify

def main():
    comparisons=[]
    L=(1,1,1,4)
    T=F(2)
    noise=(F(1,4),)*3
    for B,D in ((20,0),(20,3),(20,4),(20,5),(20,10),(1,10)):
        args=(L,F(B),F(D),noise,T)
        mixed=opt(*args,force='mixed')
        diff=opt(*args,force='only-diff')
        assert mixed[0]==F(15,4)+min(2*B,D) and diff[0]==F(31,4)
        best=opt(*args)
        assert best[0]==min(mixed[0],diff[0])
        comparisons.append(dict(B=B,D=D,mixed=mixed,differential=diff,best=best))
    return dict(checks=verify(),fixed_models=comparisons)
if __name__=='__main__':print(json.dumps(main(),sort_keys=True,default=str))
