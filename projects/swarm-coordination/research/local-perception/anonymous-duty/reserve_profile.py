"""Check the exact quotient by the readout family, with refinement failure."""
from itertools import combinations

def cap(Y, W):
    return max((W&y).bit_count() for y in Y)

def down(Y,n):
    return {s for s in range(1<<n) if any(s&y==s for y in Y)}

def main():
    n=3
    F=[tuple(y for y in range(1<<n) if h>>y&1) for h in range(1,1<<(1<<n))]
    profiles=[tuple(cap(Y,W) for W in range(1<<n)) for Y in F]
    ideals=[down(Y,n) for Y in F]
    for j,Y in enumerate(F):
        for k,Z in enumerate(F):
            assert (ideals[j]<=ideals[k])==all(a<=b for a,b in zip(profiles[j],profiles[k]))
    print(len(F)**2,'directional capacity comparisons vs downward closure')
    Y=(0b11,0b00); Z=(0b11,0b01)
    assert down(Y,2)==down(Z,2)
    assert cap(tuple(s for s in Y if not s&0b10),0b01)==0
    assert cap(tuple(s for s in Z if not s&0b10),0b01)==1
    print('same old capacity envelope; new credible absence reading splits it into reserve need 0 vs 1')
if __name__=='__main__':main()
