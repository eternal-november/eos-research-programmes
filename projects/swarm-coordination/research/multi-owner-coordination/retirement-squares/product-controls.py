"""Matched raw product search and reproduction on the pinned offline prior."""
from collections import deque
from dataclasses import replace
from signatures import Hold, observed, retire
from sys import argv,path
from os.path import join
from subprocess import check_output

def bfs(left,right,m):
    q=deque([(left,right,())]);seen={(left,right)}
    while q:
        l,r,seq=q.popleft()
        if observed(l,1)!=observed(r,1): return seq
        for i in range(m):
            a,b=retire(l,i,True),retire(r,i,True)
            if (a,b) not in seen:
                q.append((a,b,seq+(i,)));seen.add((a,b))
    return None

def main():
    for m in range(1,9):
        l,r=[[Hold(k,(1,),k) for k in range(1<<m) if k.bit_count()%2==par]
              for par in (0,1)]
        assert len(bfs(tuple(l),tuple(r),m))==m
    print('independent raw product BFS confirms minimum diagnostic depth through eight scopes')
    if len(argv)>1:
        root=argv[1]
        pin='5874e9d7c6055fa8deff6a0dcc68c10f6f952eaa'
        assert check_output(['git','-C',root,'rev-parse','HEAD'],text=True).strip()==pin
        path.insert(0,join(root,'src'))
        from holdspec.differential import find_difference
        from holdspec.profiles import P_STRIPE_DEFAULT
        from holdspec.sut import ReferencePSP
        a=replace(P_STRIPE_DEFAULT,max_release_delay=1,horizon_override=6)
        b=replace(P_STRIPE_DEFAULT,max_release_delay=2,horizon_override=6)
        result=find_difference(lambda:ReferencePSP(a),lambda:ReferencePSP(b),b,max_states=100000)
        assert result.field=='released' and result.sequence==['authorize(4)','void()'] and result.op=='advance_time(1)'
        print('actual HoldSpec offline comparison:',result.script(),result.field,result.left,result.right)

if __name__=='__main__':main()
