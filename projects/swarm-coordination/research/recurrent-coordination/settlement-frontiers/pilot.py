"""Settlement frontier for a fixed issuer. Python 3.12."""
from dataclasses import dataclass
from itertools import combinations,product
import argparse
import json
from math import comb


@dataclass(frozen=True)
class Summary:
    u:int
    f:int
    seen:frozenset  # Settled IDs above f (not the holes).

    @staticmethod
    def pack(u,f,seen):
        seen = set(i for i in seen if f < i <= u)
        while f+1 in seen:
            f+=1
            seen.remove(f)
        return Summary(u,f,frozenset(seen))

    def admits(self,i):
        return 0<i<=self.u and (i<=self.f or i in self.seen)

    def deliver(self,i):
        assert 0<i<=self.u
        return Summary.pack(self.u,self.f,self.seen|{i})

    def merge(self,b):
        return Summary.pack(max(self.u,b.u),max(self.f,b.f),self.seen|b.seen)


EMPTY=Summary(0,0,frozenset())


def reached(u,settled):
    """All physical returns happen in the prefix; deliveries alone differ."""
    s=EMPTY
    trace=[("split",0)]
    for i in range(1,u+1):
        trace.extend([("issuer_starts_support",i),("physical_rack_accepts_and_receipt_issued",i)])
        s=Summary(i,s.f,s.seen)
    trace.append(("rejoin",0))
    for i in sorted(settled):
        s=s.deliver(i)
        trace.append(("bound_receipt_delivered",i))
    return s,trace


def powerset(xs):
    xs=tuple(xs)
    for n in range(len(xs)+1):
        yield from combinations(xs,n)


def extended_history(cap,u,holes):
    """Reach any chosen sparse set with one transient extra issue slot."""
    assert 1 in holes and (len(holes)<cap or len(holes)==cap and u in holes)
    pending=set()
    q=EMPTY
    all_physical=set()
    for i in range(1,u+1):
        assert len(pending)<cap
        q=Summary(i,q.f,q.seen)
        pending.add(i)
        all_physical.add(i)  # Takes place before a deliverable typed receipt.
        if i not in holes:
            q=q.deliver(i)
            pending.remove(i)
    assert pending==set(holes) and all_physical==set(range(1,u+1))
    return q


def recurrent(b,cycles):
    """Executable physical/permission schedule. Reference keeps all records."""
    q=EMPTY
    oracle=set()
    started=set()
    returned=set()
    trace=[]
    largest=0
    def record(label,n=0):
        trace.append((label,n,q.f,q.u,sorted(q.seen),sorted(started-returned)))
        assert q.u-q.f<=b
        assert all(q.admits(i)==(i in oracle) for i in range(1,q.u+1))
        # Protect real release, not just documentary acceptance.
        assert oracle<=returned<=started
    while q.u<b*cycles:
        record("split")
        lo=q.u+1
        for i in range(lo,lo+b):
            assert q.u-q.f<b
            q=Summary(i,q.f,q.seen)
            started.add(i)
            record("support_started",i)
        # One genuine old support remains load-bearing through rejoin.
        for i in range(lo+b-1,lo,-1):
            returned.add(i)
            record("physical_acceptance",i)
        record("rejoin")
        for i in range(lo+b-1,lo,-1):
            q=q.deliver(i)
            oracle.add(i)
            record("later_receipt_first",i)
        assert lo in started-returned and q.f==lo-1 and q.u-q.f==b
        record("new_issue_refused_at_width_cap",q.u+1)
        # Replica has same fixed issuer and coherent receipt provenance;
        # act of merging learned facts is not a new physical transfer.
        returned.add(lo)
        record("old_support_physically_accepted",lo)
        assert not q.admits(lo)
        holder=Summary.pack(q.u,lo-1,{lo})
        q=q.merge(holder)
        oracle.add(lo)
        record("delivery_via_merge_enables_admission",lo)
        assert q.admits(lo) and q.f==lo+b-1
        q=q.deliver(lo)
        record("duplicate_has_no_effect",lo)
        largest=max(largest,b)
    return q,trace,largest


def oracle_sparse(u,cap):
    # Raw sets with monotone issue; refuse new issue if documentary K slots
    # full. After each issue, any non-old pending receipt can be delivered.
    active={frozenset()}
    for i in range(1,u+1):
        nxt=set()
        for holes in active:
            if len(holes)<cap:
                raw=holes|{i}
                for keep in powerset(raw-{1}):
                    nxt.add(frozenset({1,*keep}))
        active=nxt
    return active


def physical_order(events):
    holder="old"
    accepted=[]
    for e in events:
        if e=="settle" and holder=="old":
            holder=None
            accepted.append(e)
        elif e=="admit" and holder is None:
            holder="new"
            accepted.append(e)
    return holder,accepted


def checks():
    assert physical_order(("settle","admit"))==("new",["settle","admit"])
    assert physical_order(("admit","settle"))==(None,["settle"])
    assert not EMPTY.merge(EMPTY).admits(1)
    merged=0
    P=[]
    for n in range(6):
        for s in powerset(range(1,n+1)):
            q,_=reached(n,s)
            assert {i for i in range(1,n+1) if q.admits(i)}==set(s)
            P.append((n,set(s),q))
    for (n,s,a),(m,t,b) in product(P,P):
        want=Summary.pack(max(n,m),0,s|t)
        assert a.merge(b)==b.merge(a)==want
        assert want.u-want.f<=max(a.u-a.f,b.u-b.f)
        merged+=1
    dcount={}
    for b in range(1,10):
        states=[reached(b,seen)[0] for seen in powerset(range(2,b+1))]
        assert all(q.u==b and q.f==0 for q in states)
        output={tuple(q.admits(i) for i in range(2,b+1)) for q in states}
        assert len(output)==len(states)==2**(b-1)
        dcount[b]=len(states)
    # Exact sparse law: a Kth unresolved ID can survive only if it was
    # the final issue; otherwise the next issue could not have happened.
    sparse={}
    for n in (4,8,16,64):
        cap=3
        allholes=oracle_sparse(n,cap)
        expected=({frozenset({1,*xs}) for r in range(cap-1)
                    for xs in combinations(range(2,n+1),r)}
                  |{frozenset({1,n,*xs}) for xs in combinations(range(2,n),cap-2)})
        assert allholes==expected
        states=[extended_history(cap,n,h) for h in allholes]
        assert len({q.seen for q in states})==len(states)==sum(comb(n-1,j) for j in range(cap-1))+comb(n-2,cap-2)
        assert all(q.f==0 and q.u==n for q in states)
        sparse[n]=len(states)
    # Same returned/issued identity, different previous documentary delivery.
    a,_=reached(2,())
    b,_=reached(2,(2,))
    assert a.f==b.f==0 and a.u==b.u==2
    assert not a.admits(2) and b.admits(2)
    assert a.deliver(2)==b.deliver(2)==b
    # Stale retry across rejoin cannot count a second permission.
    final,example,_=recurrent(3,3)
    assert final.f==final.u==9
    sweep,_,_=recurrent(7,250)
    assert sweep.f==sweep.u==1750
    return dict(merge_compares=merged,exact_frontier_states=dcount,
                sparse_hole_states_at_cap_3=sparse,recurrence_operations=1750,
                short_trace=example)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--json",action="store_true")
    out=checks()
    print(json.dumps(out,indent=2,sort_keys=True) if p.parse_args().json else
          {k:v for k,v in out.items() if k!="short_trace"})
