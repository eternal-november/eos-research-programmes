from pathlib import Path
from hashlib import sha1
import subprocess
import tempfile
from itertools import permutations, combinations, product

PIN={"topic_handle.hpp":"a03f5cc8f01774835509c1deaba089dfa57b2531",
     "twist_mux.cpp":"2ec04da212141b6ece3629a9b9d18a5a64142013"}

def compile_source():
    h=Path(__file__).resolve().parent
    src={}
    for name,d in PIN.items():
        raw=(h/name).read_bytes()
        assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==d
        src[name]=raw.decode()
    def take(s,signature,end):
        i=s.index(signature)
        return s[i:s.index(end,i)+len(end)]
    t=src['topic_handle.hpp'];m=src['twist_mux.cpp']
    with tempfile.TemporaryDirectory() as d:
        p=Path(d)
        incs={
            'expiry':'\n'.join([take(t,'  bool hasExpired(', '\n  }')]),
            'lock':'\n'.join(take(t,s,'\n  }') for s in
                   ('  bool isLocked(', '  void callback(const std_msgs::msg::Bool::ConstSharedPtr')),
            'movement':'\n'.join(take(t,s,'\n  }') for s in
                       ('  bool isMasked(', '  void callback(const geometry_msgs::msg::Twist::ConstSharedPtr')),
            'mux':'\n'.join(take(m,s,'\n}') for s in
                  ('int TwistMux::getLockPriority(', 'bool TwistMux::hasPriority(')),
        }
        for f,body in incs.items():(p/(f+'.inc')).write_text(body+'\n')
        subprocess.run(["g++","-std=c++17","-O2","-I",d,str(h/'harness.cpp'),"-o",str(p/'check')],check=True)
        subprocess.run([str(p/'check')],check=True)

def test_architecture():
    checks=0
    for n in range(1,5):
        names=tuple(range(n))
        allowed={frozenset(k) for sz in range(n+1) for k in combinations(names,sz)}
        emittable=[]
        for order in permutations(names):
            emittable.append({frozenset(order[i:]) for i in range(n+1)})
        for k in range(1,5):
            for required in combinations(allowed,k):
                chain=all(a<=b or b<=a for a,b in combinations(required,2))
                exists=any(set(required)<=p for p in emittable)
                assert exists==chain
                checks+=1
    print('all finite mask families vs fixed priority assignment: ',checks,' checks',sep='')

def effective_baseline():
    # Required allowed/forbidden labels plus one physically forced veto bit
    # at this cut, for example from a stale lock occupying the necessary scope.
    def criterion(rows):
        live_values=set()
        for good,key,actors,forced in rows:
            if good:
                if forced:return False
                live_values.update((i,key[i]) for i,on in enumerate(actors) if on)
        return all(good or forced or any(on and (i,key[i]) not in live_values
                   for i,on in enumerate(actors)) for good,key,actors,forced in rows)
    def tables(rows):
        for m in range(16):
            if all(good==(not forced and all(not on or not (m>>(2*i+key[i])&1)
                      for i,on in enumerate(actors))) for good,key,actors,forced in rows):
                return True
        return False
    n=0
    keys=((0,1),(1,0),(0,0)) # good rows then the forbidden row
    availability=list(product((False,True),repeat=2))
    for fusion in product(availability,repeat=3):
        for forced in product((False,True),repeat=3):
            for good in product((False,True),repeat=3):
                rows=list(zip(good,keys,fusion,forced))
                assert criterion(rows)==tables(rows)
                n+=1
    print('cut-local effective C&P veto vs full local tables',n,'checks')

def axis_cover(allowed,n):
    # For each fixed order, compute the maximal set of forbidden cells
    # it can exclude without excluding any row's allowed cells. Then
    # search combinations of independently configurable scalar gates.
    items=tuple(range(n))
    forbidden=tuple((i,j) for i,r in enumerate(allowed) for j in items if j not in r)
    edges=set()
    for order in permutations(items):
        pos={a:i for i,a in enumerate(order)}
        earliest=[min((pos[a] for a in row),default=n) for row in allowed]
        edges.add(sum(1<<k for k,(i,j) in enumerate(forbidden) if pos[j]<earliest[i]))
    target=(1<<len(forbidden))-1
    if not target:return 0
    layer={0}
    for k in range(1,n+1):
        layer={x|y for x in layer for y in edges}
        if target in layer:return k
    raise AssertionError('axis-by-axis exclusion must suffice')
for n in range(2,7):
    sets=[frozenset({i}) for i in range(n)]
    compliments=[frozenset(range(n))-{i} for i in range(n)]
    assert axis_cover(sets,n)==2
    assert axis_cover(compliments,n)==n
print('parallel threshold gates: choose exactly one = two; omit exactly one = n (checked n=2..6)')

if __name__=='__main__':
    compile_source()
    test_architecture()
    effective_baseline()
