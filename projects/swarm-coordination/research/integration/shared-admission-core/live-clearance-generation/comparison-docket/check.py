"""Verify pinned integration verdicts and a held-in evidence discriminator."""
from functools import cache
from pathlib import Path
import hashlib
import json
import sys

root=Path(sys.argv[1])
data={}
for line in Path(__file__).with_name("SOURCE.tsv").read_text().splitlines():
    name,repo,rev,path,expected=line.split("\t")
    b=(root/name).read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==expected
    data[name.removesuffix(".json")]=json.loads(b)

v=lambda n:data[n]["verdicts"]
def metrics():
    cut=data["consuming-cut"]["stats"]
    assert cut["scoped"]==cut["direct"] and cut["scoped"]["paid"]==1960
    lease=v("source-step-lease")
    assert lease["composed"]==lease["direct"] and lease["composed"]["delivered"]==700
    pledge=v("terminal-pledge")
    assert pledge["pledge"]==pledge["direct"] and pledge["pledge"]["side_at_one"]==7560
    recur=v("native-recurring-request")
    assert recur["effect-key"]["old_exact"]==40 and recur["replay-all"]["duplicate"]==20
    commit=data["native-atomic-commit"]["summary"]
    assert commit["bundled"]["exact"]==16 and commit["split"]["exact"]==12
    live=v("durable-terminal-release")
    assert live["durable"]==live["direct"] and live["durable"]["returned"]==40
    final=v("pre-settlement-failover")
    assert final["staged"]==final["direct"] and final["staged"]["service"]==20
    assert final["reactive"]["service"]==16
    return dict(failover_staged=20,failover_staged_direct=20,failover_reactive=16,
                audited_replays=len(data),independent_evaluations_consumed=0)

def example():
    letters="abcdef"
    f=[sum(1<<letters.index(x) for x in xs) for xs in ("adf","bcd","cef","bf","abe")]
    full=(1<<len(letters))-1
    parents=[(i,j) for i in range(6) for j in range(i) if any(
                 (p&((1<<i)|(1<<j)))==((1<<i)|(1<<j)) for p in f)]
    seen={0}
    while True:
        extended=seen|{j for i,j in parents if i in seen}|{i for i,j in parents if j in seen}
        if extended==seen:break
        seen=extended
    assert len(seen)==6
    worlds={(truth,flips^(full if truth else 0)) for truth in (0,1)
            for allowed in f for flips in range(full+1) if flips&~allowed==0}
    table={v:any(v&~allowed==0 for allowed in f) for v in range(full+1)}

    static=[]
    for v in range(full+1):
        r=[{truth for truth,pattern in worlds if (pattern&v)==x}
           for x in {p&v for _,p in worlds}]
        fits=all(len(bits)==1 for bits in r)
        assert fits==all(v&~(a|b)!=0 for a in f for b in f)
        if fits:static.append(v)
    assert static==[full]

    @cache
    def policy(zeros,ones):
        if not table[zeros] or not table[ones]:return 0,-1
        return min((1+max(policy(zeros|q,ones)[0],policy(zeros,ones|q)[0]),j)
                   for j in range(6) if not (zeros|ones)&(q:=1<<j))

    # Independent oracle splits explicit possible truth/report worlds,
    # using a depth budget rather than the min-cost recurrence above.
    @cache
    def fits(ws,remaining,depth):
        if len({v[0] for v in ws})<=1:return True
        if not depth:return False
        for j in range(6):
            q=1<<j
            if remaining&q and all(fits(tuple(w for w in ws if bool(w[1]&q)==bit),
                                    remaining^q,depth-1) for bit in (False,True)):
                return True
        return False
    ordered=tuple(sorted(worlds))
    # Cross-check every partial decision state, including readings which
    # no allowed world could produce, and all finite horizons.
    from itertools import product
    for read in product((-1,0,1),repeat=6):
        z=sum(1<<i for i,k in enumerate(read) if k==0)
        o=sum(1<<i for i,k in enumerate(read) if k==1)
        w=tuple(w for w in ordered if w[1]&z==0 and w[1]&o==o)
        for horizon in range(7):
            assert (policy(z,o)[0]<=horizon)==fits(w,full^(z|o),horizon)

    steps=[]
    for truth,pattern in ordered:
        z=o=reads=0
        while table[z] and table[o]:
            j=policy(z,o)[1]
            if pattern&(1<<j):o|=1<<j
            else:z|=1<<j
            reads+=1
        assert int(table[z])==truth
        steps.append(reads)
    minimum,first=policy(0,0)
    assert minimum==max(steps)==5
    return dict(reports=letters,fail_sets=["adf","bcd","cef","bf","abe"],
                component_count=1,worlds=len(worlds),fixed_minimum=6,
                adaptive_minimum=minimum,first=letters[first],
                checked_partial_horizons=3**6*7)

print(json.dumps(dict(replay=metrics(),held_in=example()),sort_keys=True))
