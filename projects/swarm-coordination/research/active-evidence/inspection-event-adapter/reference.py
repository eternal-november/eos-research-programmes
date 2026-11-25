"""Uncompressed direct policy enumeration on the same source actions."""
from collections import defaultdict
from functools import cache
from itertools import product
from mission import Fixture,synth,execute
from checks import seed

def reference(f):
    worlds=list(range(len(f.worlds)))
    @cache
    def all_ok(group):
        t=group[0][1].tick
        if any(s.failed for i,s in group):return False
        if any(t>=r["deadline"] and name not in dict(s.delivered)
               for i,s in group for name,r in f.reports.items()):return False
        if t==f.d["egress_due"]:return all(f.done(s) for i,s in group)
        # Current local receipts may split an existing history but never
        # identify which scenario index the runtime controller inhabits.
        cohorts=defaultdict(list)
        for i,s in group:cohorts[f.observe(i,s)].append((i,s))
        return all(any(all_ok(tuple((i,f.step(i,s,a)) for i,s in C))
                   for a in set.intersection(*(set(f.choices(s)) for i,s in C)))
                   for C in cohorts.values())
    return all_ok(tuple((i,f.initial(i)) for i in worlds))

def tests():
    n=0
    for act_d,link_t,need,ack_out,fed in product(
            (1,2),(4,6,9),("none","physical","record"),(False,True),(False,True)):
        d=seed(B=8,H=11,p_feed=fed);d["round_d"]=act_d
        for e in d["arcs"]:
            if e["dst"]=="base" and need!="none":
                e["need_delivered" if need=="physical" else "need_receipts"]=["A","B"]
        for w in d["worlds"]:
            w["radio_down"]={"r1":[[link_t,link_t+1]]}
            if ack_out:w["radio_down"]["ack"]=[[2,12]]
        f=Fixture(d)
        found=synth(f,extract=True)
        assert bool(found)==reference(f),(act_d,link_t,need,ack_out,fed)
        if found:
            for i in range(len(f.worlds)):execute(f,i,found)
        n+=1
    print(n,"source-equal direct policy checks with variable event timing and egress requirements")

def old_summary():
    # Same actual custody in two simulations, one policy's old status cannot
    # satisfy a later authority predicate requiring a recognized receipt.
    b=seed(6,10)
    for w in b["worlds"]:w["radio_down"]={"ack":[[2,20]]}
    for e in b["arcs"]:
        if e["dst"]=="base":e["need_delivered"]=["A","B"]
    f=Fixture(b);P=synth(f,extract=True);assert P
    for i in range(len(f.worlds)):
        row=execute(f,i,P);assert row[-1][-1].delivered and not row[-1][-1].receipts
    for e in b["arcs"]:
        if e["dst"]=="base":e["need_receipts"]=["A","B"]
    assert not synth(Fixture(b))
    print("actual delivery with a lost ACK satisfies the physical law, not the added receipt-to-egress law")

if __name__=="__main__":tests();old_summary()
