"""Conditional exact coding behind a native audit aperture."""
from collections import Counter,defaultdict
from functools import lru_cache
from itertools import product
import json

def bits(count):
    assert count>=1
    return (count-1).bit_length()

@lru_cache(None)
def avoiding(n,r):
    if n==0:return 1
    states=[1]+[0]*(r-1)
    for _ in range(n):states=[sum(states)]+states[:-1]
    return sum(states)

def distributions(n,r):
    """Histogram: old answers counted by the number of exact source histories."""
    m=n-r+1
    def push(dst,f,sub):
        for k,v in sub.items():dst[f*k]+=v
    @lru_cache(None)
    def inside(t):
        if not t:return Counter({1:1})
        out=inside(t-1).copy()
        out[avoiding(t-1,r)]+=1 # positive tail, bounded only at left
        for l in range(r,t):
            push(out,avoiding(max(0,l-r-1),r),inside(t-l-1))
        return out
    out=inside(m-1).copy() # initial 0
    out[avoiding(n,r)]+=1  # all positive
    for l in range(1,m):push(out,avoiding(l-1,r),inside(m-l-1))
    return out,inside

def hist(n,r):return distributions(n,r)[0]

def summary(hist,b):
    return sum(((k+(1<<b)-1)>>b)*v for k,v in hist.items())

def need(h,a):
    if sum(h.values())>1<<a:return None
    hi=bits(max(h));lo=0
    while lo<hi:
        b=(lo+hi)//2
        if summary(h,b)<=1<<a:hi=b
        else:lo=b+1
    return lo

def width(x,r):
    return tuple(int(any(x[i:i+r])) for i in range(len(x)-r+1))

def fibers(n,r):
    out=defaultdict(list)
    for x in product((0,1),repeat=n):out[width(x,r)].append(x)
    return out

def runs(ordered):
    last=-2
    for i,k in enumerate(ordered):
        assert k>last
        if k!=last+1:
            if i:yield size
            size=0
        size+=1;last=k
    if ordered:yield size

def flip_positions(y,r):
    return frozenset(j for i,b in enumerate(y) if not b for j in range(i,i+r))

@lru_cache(None)
def suffix_count(n,r,trail):
    if n==0:return 1
    return suffix_count(n-1,r,0)+(suffix_count(n-1,r,trail+1) if trail+1<r else 0)

def rank(word,r):
    a=0;trail=0
    for i,b in enumerate(word):
        if b:
            if trail+1<r:a+=suffix_count(len(word)-i-1,r,trail+1)
            trail=0
        else:
            trail+=1
            assert trail<r
    return a

def decode(n,r,a):
    assert 0<=a<avoiding(n,r)
    out=[];trail=0
    for i in range(n):
        low=suffix_count(n-i-1,r,trail+1) if trail+1<r else 0
        if a<low:out.append(0);trail+=1
        else:out.append(1);trail=0;a-=low
    assert a==0
    return tuple(out)

def supplement(n,r,y,ix,word):
    z=flip_positions(y,r)
    assert len(ix)==len(word)
    flipped=tuple(1 if i in z else b for i,b in zip(ix,word))
    a=0;off=0
    for l in runs(ix):
        a=a*avoiding(l,r)+rank(flipped[off:off+l],r);off+=l
    return a

def unsupplement(n,r,y,ix,a):
    z=flip_positions(y,r)
    pieces=[]
    for l in reversed(tuple(runs(ix))):
        a,b=divmod(a,avoiding(l,r));pieces.extend(reversed(decode(l,r,b)))
    assert a==0
    return tuple(0 if i in z else b for i,b in zip(ix,reversed(pieces)))

def source_code(n,r,y):
    """Lexicographic enumeration for past answer fixed, with no source oracle."""
    def allowed(i,t):
        return i<r-1 or y[i-r+1]==int(t<r)
    @lru_cache(None)
    def cnt(i,t):
        if i==n:return 1
        return sum(cnt(i+1,s) for s in (min(r,t+1),0) if allowed(i,s))
    def encode(word):
        rank=0;t=0
        for i,b in enumerate(word):
            z=min(r,t+1)
            if b and allowed(i,z):rank+=cnt(i+1,z)
            t=0 if b else z
            assert allowed(i,t)
        return rank
    def decode(rank):
        assert 0<=rank<cnt(0,0)
        out=[];t=0
        for i in range(n):
            z=min(r,t+1)
            low=cnt(i+1,z) if allowed(i,z) else 0
            if rank<low:out.append(0);t=z
            else:out.append(1);t=0;rank-=low
            assert allowed(i,t)
        return tuple(out)
    return encode,decode,cnt(0,0)

def two_stage(n,r,b):
    """Return enc/early-dec/late-dec for a preauthorized richer first code."""
    histogram,interior=distributions(n,r)
    m=n-r+1;block=1<<b
    def branches(t,first):
        yield (0,),1,False
        yield (1,)*t,avoiding(n if first else t-1,r),True
        for l in range(1 if first else r,t):
            e=l-1 if first else max(0,l-r-1)
            yield (1,)*l+(0,),avoiding(e,r),False
    @lru_cache(None)
    def slots(t,scale):
        return sum(((scale*f+block-1)//block)*count for f,count in interior(t).items())
    def bases(y):
        pos=0;prod=1;base=0
        while pos<m:
            found=False
            for pre,f,terminal in branches(m-pos,pos==0):
                local=pos+len(pre);scaled=prod*f
                if tuple(y[pos:local])==pre:
                    pos=local;prod=scaled;found=True;break
                base+=slots(0 if terminal else m-local,scaled)
            assert found
        return base,prod
    def early(rank):
        assert 0<=rank<summary(histogram,b)
        y=();prod=1
        while len(y)<m:
            for pre,f,terminal in branches(m-len(y),not y):
                after=m-len(y)-len(pre);scaled=prod*f
                count=slots(0 if terminal else after,scaled)
                if rank<count:
                    y+=pre;prod=scaled;break
                rank-=count
            else:raise AssertionError('rank outside tree')
        return y,rank
    def encode(x):
        y=width(x,r)
        base,prod=bases(y)
        enc,_,f=source_code(n,r,y)
        assert f==prod
        high,low=divmod(enc(x),block)
        return base+high,low
    def late(first,rest):
        y,h=early(first)
        _,dec,_=source_code(n,r,y)
        return dec(h*block+rest)
    return encode,early,late

def test():
    exact_small=0;checked_subsets=0;checked_codes=0;stage_checks=0
    for n in range(1,12):
        for r in range(1,n+1):
            fs=fibers(n,r);h=hist(n,r)
            assert h==Counter(map(len,fs.values()))
            exact_small+=1
            if n>8:continue
            b=need(h,bits(sum(h.values())))
            enc,early,late=two_stage(n,r,b)
            for y,rows in fs.items():
                for x in rows:
                    a,t=enc(x)
                    assert early(a)[0]==y and late(a,t)==x
                    stage_checks+=1
            for mask in range(1<<n):
                ix=tuple(i for i in range(n) if mask>>i&1)
                k=1
                for l in runs(ix):k*=avoiding(l,r)
                max_size=0
                for y,ls in fs.items():
                    proj={tuple(x[i] for i in ix) for x in ls}
                    max_size=max(max_size,len(proj))
                    for z in proj:
                        a=supplement(n,r,y,ix,z)
                        assert 0<=a<k
                        assert unsupplement(n,r,y,ix,a)==z
                        checked_codes+=1
                assert max_size==k
                checked_subsets+=1
    return dict(histograms=exact_small,subsets=checked_subsets,codes=checked_codes,staged_code_round_trips=stage_checks)

def main():
    checks=test();rows=[]
    for n,r in ((6,2),(12,5),(24,5),(48,5),(100,5)):
        h=hist(n,r)
        assert sum(k*v for k,v in h.items())==1<<n
        a=bits(sum(h.values()));b=need(h,a)
        assert b is not None
        rows.append(dict(rounds=n,width=r,old_answer_count=sum(h.values()),max_fiber=max(h),
            initial_bits=a,plain_supplement_bits=bits(max(h)),redesigned_supplement_bits=b,
            initial_codewords_at_bound=summary(h,b),initial_codewords_one_fewer=summary(h,b-1) if b else None,
            cardinalities=len(h)))
    n,r=100,5
    enc,early,late=two_stage(n,r,53)
    vects=[tuple(int((i*j)%q>=p) for i in range(n))
           for j,q,p in ((1,2,1),(1,1,0),(1,1,1),(1,11,7),(5,9,4),(7,19,8))]
    for x in vects:
        a,b=enc(x)
        assert a<1<<54 and b<1<<53
        assert early(a)[0]==width(x,r) and late(a,b)==x
    print(json.dumps(dict(checks=checks,cases=rows,large_staged_round_trips=len(vects),contiguous_50_bits=bits(avoiding(50,5)),
                    alternating_50_bits=50),sort_keys=True,separators=(',',':')))
if __name__=='__main__':main()
