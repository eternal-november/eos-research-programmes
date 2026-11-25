"""Exact single effect-side interlock retries in a declared physical timing model."""
from itertools import combinations,permutations
from random import Random

# Route fields: worst successful completion and failed-source release latency.
# A failed hold expires only when real re-entry is authorized and completion
# versus failure is actually separated. Status ACK is an untrusted projection.
def fixed_order(routes,ids):
    elapsed=0;ends=[]
    for i in ids:
        success,release=routes[i]
        ends.append(elapsed+success);elapsed+=release
    return max(ends,default=0)

def exhaustive(routes,f):
    return min((fixed_order(routes,ix),ix) for ix in permutations(range(len(routes)),f+1))

def feasible(routes,f,deadline):
    order=sorted(range(len(routes)),key=lambda i:routes[i][1]-routes[i][0])
    best={0:(0,())}
    for i in order:
        s,d=routes[i]
        for k,(used,ids) in sorted(tuple(best.items()),reverse=True):
            if k>f or used+s>deadline: continue
            x=used+d,ids+(i,)
            if k+1 not in best or x<best[k+1]:best[k+1]=x
    return best[f+1][1] if f+1 in best else None

def optimum(routes,f):
    l=0
    u=sum(x[1] for x in routes)+max(x[0] for x in routes)
    while l<u:
        mid=(l+u)//2
        if feasible(routes,f,mid) is None:l=mid+1
        else:u=mid
    return l,feasible(routes,f,l)

def physical(routes,ids,fail,unsafe_ack=None):
    # Source event sequence; physically occupied interlock excludes reentry.
    # Now is the actor's decision time based on actual certified release,
    # or the deliberately bad last-status projection if explicitly selected.
    trace=[];now=free=0
    for i in ids:
        if now<free:return None,trace
        trace.append((now,'physically acquired',i))
        s,d=routes[i]
        if i not in fail:
            trace.append((now+s,'official committed effect',i))
            return now+s,trace
        free=now+d
        trace.append((free,'physical retirement',i))
        now=free if unsafe_ack is None else now+unsafe_ack[i]
    return None,trace

def main():
    rng=Random(633913)
    n=0
    for _ in range(2900):
        k=rng.randrange(2,8);f=rng.randrange(k)
        routes=tuple((rng.randrange(1,13),rng.randrange(1,13)) for _ in range(k))
        cost,order=optimum(routes,f)
        assert cost==exhaustive(routes,f)[0]
        assert max(physical(routes,order,set(bad))[0] for bad in combinations(range(k),f))==cost
        n+=1
    print(n,'exact route subset/schedule comparisons and same-world effect traces')
    poss=((5,2),(2,5))
    assert optimum(poss,1)==(5,(0,1))
    # A status-only failure bound can both change the choice and certify a
    # promise that the actual actuator misses.
    actually=((4,8),(5,2))
    wrong=((4,1),(5,2))
    right=optimum(actually,1)
    alt=optimum(wrong,1)
    assert right==(6,(1,0)) and alt==(6,(0,1))
    assert physical(actually,alt[1],{0},(1,2))[0] is None
    assert physical(actually,alt[1],{0})[0]==13
    print('actual physical release chooses order',right[1],'vs ACK-only',alt[1],
          'and ACK-only order needs time 13, not its declared 6')
if __name__=='__main__':main()
