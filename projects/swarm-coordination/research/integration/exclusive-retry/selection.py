"""First local-selector probe: own readiness is not exclusive ownership."""
from itertools import combinations
from scipy.optimize import linprog

def allowed_masks(worlds,n):
    return [q for q in range(1<<n) if all((q&w).bit_count()<=1 for w in worlds)]

def certain(worlds,n):
    return [q for q in allowed_masks(worlds,n) if all((q&w).bit_count()==1 for w in worlds)]

def minimax(worlds,n):
    m=allowed_masks(worlds,n)
    # Exogenous shared randomness independent of source type, with hard
    # collision-freedom in each admissible source history. Optimize service.
    A=[[-int(bool(w&q)) for q in m]+[1] for w in worlds]
    r=linprog([0]*len(m)+[-1],A_ub=A,b_ub=[0]*len(worlds),
              A_eq=[[1]*len(m)+[0]],b_eq=[1],bounds=[(0,1)]*(len(m)+1),method='highs')
    assert r.success
    return r.x[-1]

def main():
    assert certain([1,2],2)==[3]
    assert not certain([1,2,3],2)
    cases=0
    for n in range(2,9):
        for k in range(1,n+1):
            w=[sum(1<<a for a in combo) for size in range(k,n+1)
                        for combo in combinations(range(n),size)]
            assert abs(minimax(w,n)-k/n)<1e-10
            cases+=1
    print(cases,'matched randomized hard exclusivity cases')
    print('one live out of two suffices only if both-live possibility is excluded or an arbiter is added')
if __name__=='__main__':main()
