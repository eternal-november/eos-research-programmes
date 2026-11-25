"""Civil bay fixture. Compare an event expansion to the timed bounds."""
from fractions import Fraction as Q
from itertools import product


def event_run(notice, key, clears, outbound, inbound, work, expiry, deadline):
    req = rsp = start = finish = None
    for now in range(deadline + 1):
        if req is None and now >= notice and now >= key and now <= expiry:
            req = now + outbound
        if req is not None and req <= now and now >= clears and rsp is None:
            rsp = now + inbound
        if rsp is not None and rsp <= now and start is None:
            if now + work <= expiry:
                start = now
                finish = now + work
        if finish == now:
            return finish
    return None


def deterministic():
    count = 0
    for report in product(range(3), repeat=2):
        for raw in product((0, 1), repeat=6):
            act = (raw[:3], raw[3:])
            private = report[0] == report[1]
            exact = all(act[q][report[p]] == p*q for p,q in product(range(2),repeat=2))
            assert not (private and exact)
            count += 1
    assert count == 576
    print(count, "deterministic one-way protocols: none exact and private")


def tv(p,q):
    return sum(abs(x-y) for x,y in zip(p,q))/2


def randomized():
    for e in (Q(k,32) for k in range(33)):
        # Records are no disclosure, negative and positive.
        p0,p1=(1-e,e,Q(0)),(1-e,Q(0),e)
        assert tv(p0,p1)==e
        for rr in product((Q(k,8) for k in range(9)),repeat=3):
            false=sum(x*y for x,y in zip(p0,rr))
            miss=1-sum(x*y for x,y in zip(p1,rr))
            assert false+miss>=1-e
        guess=(Q(1,2),0,1)
        assert sum(x*y for x,y in zip(p0,guess))==(1-e)/2
        assert 1-sum(x*y for x,y in zip(p1,guess))==(1-e)/2
        hard0,hard1=(1,0),(1-e,e)
        assert tv(hard0,hard1)==e and hard0[1]==0 and hard1[1]==e
    print("33 privacy budgets, 24057 randomized decision comparisons, both sharp bounds")


def timed():
    count = 0
    for notice,key,clears,a,b,h,e,D in product(
        range(5),range(5),range(7),range(4),range(4),range(3),range(7),range(9)
    ):
        f=max(clears,max(notice,key)+a)+b+h
        assert event_run(notice,key,clears,a,b,h,e,D)==(f if f<=min(e,D) else None)
        count+=1
    assert event_run(1,4,5,2,2,1,20,9)==9
    assert event_run(1,4,5,2,2,1,20,8) is None
    assert event_run(1,1,5,2,2,1,20,8)==8
    assert event_run(1,1,7,1,1,1,20,20)==9
    assert event_run(1,1,2,1,1,1,20,20)==4
    print(count,"timed source runs checked with local role activation, lease and actual clearance")
    print("actual role activation can move finish 8 -> 9; false clearance predicts 4 instead of 9")


if __name__=="__main__":
    deterministic()
    randomized()
    timed()

