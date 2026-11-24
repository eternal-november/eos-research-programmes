from itertools import combinations, product

# Survivors have fixed order and never cross the stopped body.
# Radio links are distance-limited, not blocked by the body in this class.
def local_domains(xs,f,g,T):
    L=xs[-1]
    out=[]
    for i,x in enumerate(xs):
        lo,hi=(x,x) if i in (0,len(xs)-1) else (max(0,x-T),min(L,x+T))
        if x<f: hi=min(hi,f-g)
        else: lo=max(lo,f+g)
        out.append((lo,hi))
    return out

def factor(xs,f,g,r,T):
    a,b=local_domains(xs,f,g,T)[0]
    if a>b or r<g:return False
    for lo,hi in local_domains(xs,f,g,T)[1:]:
        a,b=max(lo,a+g),min(hi,b+r)
        if a>b:return False
    return True

def exact(xs,f,g,r,T):
    ok=local_domains(xs,f,g,T)
    for p in product(*(range(a,b+1) for a,b in ok)):
        if all(g<=y-x<=r for x,y in zip(p,p[1:])): return True
    return False

n=0
for L,N,g,r,T in product(range(5,9),range(3,6),range(1,3),range(1,5),range(4)):
    for parts in combinations(range(1,L),N-1):
        full=(0,*parts,L)
        if any(y-x<g for x,y in zip(full,full[1:])):continue
        for f in parts:
            xs=tuple(x for x in full if x!=f)
            assert factor(xs,f,g,r,T)==exact(xs,f,g,r,T)
            n+=1
print(n,"exhaustive configurations match exact interval propagation")
xs=(0,2,7,9); f=4; g=1
for reach,T in product((1,2,3),(0,1,2)):
    print(f"range={reach} urgency={T} reachable connected state={factor(xs,f,g,reach,T)}")
