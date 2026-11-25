"""Minimal public advice in the zero-interlock, known-local-readiness model."""
from scipy.optimize import milp, LinearConstraint, Bounds

def support(n,k):
    return tuple(w for w in range(1<<n) if w.bit_count()>=k)

def covered(w,m):return (w&m).bit_count()==1

def solver(n,k):
    worlds=support(n,k)
    columns=tuple(range(1,1<<n))
    model=milp([1]*len(columns),integrality=[1]*len(columns),
               bounds=Bounds(0,1),
               constraints=LinearConstraint([[int(covered(w,m)) for m in columns] for w in worlds],1,float('inf')))
    assert model.success
    return round(model.fun)

def eliminate(n,k,library):
    # Any valid family must supply a new row each time: previous witness rows
    # contain no candidate left after their isolated column is deleted.
    live=(1<<n)-1;seen=set()
    while live.bit_count()>=k:
        m=next(m for m in library if covered(live,m))
        assert m not in seen
        seen.add(m);live^=live&m
    return len(seen)

def receive(cred,expected_scope,expected_epoch,live):
    if cred is None or cred[:2]!=(expected_scope,expected_epoch):return 0
    return live&cred[2]

def main():
    checks=0
    for n in range(1,8):
        for k in range(1,n+1):
            lib=tuple(1<<i for i in range(n-k+1))
            assert all(any(covered(w,m) for m in lib) for w in support(n,k))
            assert eliminate(n,k,lib)==n-k+1
            assert solver(n,k)==n-k+1
            for w in support(n,k):
                cmd=next(m for m in lib if covered(w,m))
                assert receive(('joint-service',4,cmd),'joint-service',4,w).bit_count()==1
                assert receive(('old-service',4,cmd),'joint-service',4,w)==0
                assert receive(('joint-service',3,cmd),'joint-service',4,w)==0
            checks+=1
    print(checks,'known-local-readiness advice cardinalities independently checked by MILP')
    print('eight candidates, at least three live: six symbols, so three reliable bits in this decoder')
if __name__=='__main__':main()
