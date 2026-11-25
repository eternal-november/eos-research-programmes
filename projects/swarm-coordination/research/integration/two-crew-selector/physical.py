"""A masked late detent fault, checked through two civil physical effects."""
from selector import Source,path,solve,oracle
from itertools import product

def report_setup(n,world,cut,recipient):
    # A single physical detector reports which side of a marked detent cut
    # the plant reached, only to the wired recipient before commitment.
    # Returning neither is the late/private-to-unconsumed case.
    base=path(n)
    a,b=base.edges[world]
    v=(a,b);b=(int(world>=cut),)
    return tuple((x,*b) if c in recipient else (x,) for c,x in enumerate(v))

def refinement(S,n,cut,recipients):
    L=[{},{}]; avail=[[],[]]; E=[]
    for e,(u,v) in enumerate(S.edges):
        out=[]
        for i,(z,view) in enumerate(zip((u,v),report_setup(n,e,cut,recipients))):
            if view not in L[i]:
                L[i][view]=len(avail[i]);avail[i].append((S.left,S.right)[i][z])
            out.append(L[i][view])
        E.append(tuple(out))
    return Source(tuple(E),tuple(avail[0]),tuple(avail[1]))

def finish(S,n,world,choice,mode):
    allowed=(S.left[S.edges[world][0]],S.right[S.edges[world][1]])
    assert all(p in a for p,a in zip(choice,allowed))
    occupied=set(); actual=[False,False]
    if mode=='archive':
        # Real output is the verified copy at its chosen physical recorder.
        # Sources retain their own old authentic packet until this event.
        copy=[True,True];old=copy[:]
        for i,p in enumerate(choice):
            if p in occupied:continue # hardware interlock
            occupied.add(p);actual[i]=True
            old[i]=False
        assert all(o or k for o,k in zip(old,actual))
        assert all(int(o)+int(k)==1 for o,k in zip(old,actual))
    elif mode=='cooling':
        # Two loads each are owed two units on this slot; each new physical
        # side has one dedicated unit, and the chosen branch can supply its
        # second. A failed allocation leaves the two-unit old fallback alive
        # till after the settlement window, instead of energizing an empty line.
        old_draw=[2,2]; new_draw=[0,0]
        for i,p in enumerate(choice):
            if p in occupied:continue
            occupied.add(p); actual[i]=True
            new_draw[i]=1+1
            old_draw[i]=0
        assert all(a+b==2 for a,b in zip(old_draw,new_draw))
    else:raise ValueError(mode)
    return tuple(actual)

def main():
    ncheck=0
    for n in range(2,39):
        S=path(n)
        for cut in range(1,n):
            for rec in ((),(0,),(1,),(0,1)):
                target=refinement(S,n,cut,rec)
                m,w=solve(target)
                works=(cut%2 in rec)
                assert (m is not None)==works
                if n<=6:assert (oracle(target) is not None)==works
                if works:
                    for j,(o,p) in enumerate(target.edges):
                        a=(m[(0,o)],m[(1,p)])
                        for k in ('archive','cooling'):
                            assert finish(S,n,j,a,k)==(True,True)
                            ncheck+=1
    for n in range(2,12):
        S=path(n)
        # The independent illustration chooses each locally legal handler's
        # first available port, without checking each world's joint occupancy.
        for e,(a,b) in enumerate(S.edges):
            c=(S.left[a][0],S.right[b][0])
            for k in ('archive','cooling'):
                got=finish(S,n,e,c,k)
                assert sum(got)==(2 if c[0]!=c[1] else 1)
    print(ncheck,'physical dual-source effect checks after correct report routing')
    print('exactly the receiver owning the split observation needs the bit; late or wrong recipient does not repair')
    print('local controllers can both be lawful yet one effect is refused by the shared physical gate')
if __name__=='__main__':main()
