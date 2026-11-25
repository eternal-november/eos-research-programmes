"""Protected-load admission from source histories, not from track labels.

A and B arrive with one duty each. The single-use settlement socket works
only on the resident's physical load. 'Before' means there is an unobserved
possible exchange after the socket fires; 'after' means its resident has
not moved relative to the final camera view. The camera sees both positions,
not the cart names. Reports certify the physical event, not just a command.
"""
from itertools import product

def local(phase, allowed_sides):
    # 0 = inside.  'u' interleaves behind either cut, with no source report.
    source_phases={'after':(0,), 'before':(0,1), 'u':(0,1)}
    W=set()
    for inside,side,exchange in product((0,1),allowed_sides,source_phases[phase]):
        settled=inside^side
        final_inside=inside^exchange
        pending=1-settled
        W.add((final_inside,pending))
    return W

def summarize(phase, allowed_sides):
    # After a possible unobserved exchange, both demand outcomes remain.
    if phase!='after' or len(allowed_sides)==2:return (0,1)
    return (allowed_sides[0],)*2

def direct(worlds):
    return {sum(inside==pending for inside,pending in world)
            for world in product(*worlds)}

def main():
    for phase in ('after','before'):
        for s in (0,1):
            W=local(phase,(s,))
            assert {w[0] for w in W}=={0,1}
            assert {w[1] for w in W}=={0,1}
            print(phase,'socket',s, 'protected demand', sorted(direct([W])))
    count=0
    branches=tuple(product(('after','before','u'),((0,),(1,),(0,1))))
    for n in range(1,5):
        for row in product(branches,repeat=n):
            B=direct([local(*r) for r in row])
            lo,hi=map(sum,zip(*(summarize(*r) for r in row)))
            assert B==set(range(lo,hi+1))
            for capacity in range(n+2):
                for new in (0,1):
                    assert (hi+new<=capacity)==all(v+new<=capacity for v in B)
                    count+=1
    print(count,'explicit joint history vs local recurrence admission checks')
if __name__=='__main__':main()
