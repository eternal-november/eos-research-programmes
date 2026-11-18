"""Finite quiet-window construction on an actual common elapsed-time line."""
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations
import json
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def number(x):
    if type(x) not in (int, Q):
        raise TypeError("Expected a rational time or count")
    return Q(x)


@dataclass(frozen=True)
class Interval:
    start: Q
    stop: Q

    def __post_init__(self):
        object.__setattr__(self, "start", number(self.start))
        object.__setattr__(self, "stop", number(self.stop))
        require(self.start <= self.stop, "Reversed physical interval")

    @property
    def width(self):
        return self.stop - self.start


def union_and_gaps(domain, records):
    """Each supplied closed interval covers its complete interfering support."""
    clipped = []
    for row in records:
        a, b = max(domain.start, row.start), min(domain.stop, row.stop)
        if a <= b:
            clipped.append(Interval(a,b))
    blocked = []
    for row in sorted(clipped, key=lambda x: (x.start, x.stop)):
        if blocked and row.start <= blocked[-1].stop:
            blocked[-1] = Interval(blocked[-1].start,max(blocked[-1].stop,row.stop))
        else:
            blocked.append(row)
    edges = [domain.start] + [x for row in blocked for x in (row.start,row.stop)] + [domain.stop]
    gaps = [Interval(a,b) for a,b in zip(edges[::2],edges[1::2])]
    require(len(gaps) == len(blocked)+1 and
            sum(x.width for x in blocked+gaps) == domain.width, "Incomplete cut")
    return blocked,gaps


def witness(domain, records, q):
    q = number(q)
    require(q > 0, "Positive uninterrupted job time required")
    blocked,gaps = union_and_gaps(domain, records)
    for g in gaps:
        if g.width > q:
            e = (g.width-q)/2
            result = Interval(g.start+e,g.stop-e)
            require(result.width == q and all(result.stop<b.start or b.stop<result.start for b in blocked),
                    "Boundary disturbance meets the purported closed interval")
            return result
    return None


@dataclass(frozen=True)
class Profile:
    """M(L)<=count+slope*L; total covered elapsed time<=busy+duty*L."""
    count: int
    slope: Q
    busy: Q = Q(0)
    duty: Q = Q(0)

    def __post_init__(self):
        require(type(self.count) is int and self.count >= 0, "Invalid initial count")
        for name in ("slope","busy","duty"):
            value=number(getattr(self,name))
            require(value>=0,"Negative physical budget")
            object.__setattr__(self,name,value)

    def plus(self, other):
        return Profile(self.count+other.count,self.slope+other.slope,
                       self.busy+other.busy,self.duty+other.duty)

    @classmethod
    def episodes(cls, count, slope, duration):
        d=number(duration)
        require(d>=0,"Negative episode length")
        return cls(count,slope,count*d,slope*d)

    def first_sufficient_integer(self, q):
        q=number(q)
        require(q>0,"Positive job time required")
        left=1-self.duty-q*self.slope
        if left<=0:
            return None
        limit=(self.busy+q*(self.count+1))/left
        return limit.numerator//limit.denominator+1

    def verify(self, length, q):
        L,q=number(length),number(q)
        require(L>=0 and q>0,"Invalid horizon")
        return L-self.busy-self.duty*L > q*(self.count+1+self.slope*L)


def point(name):
    if name=="B":
        b=json.loads((HERE/"return_itinerary_results.json").read_text())["budget"]
        return {k:Q(b[v]) for k,v in (("q","quiet_gap"),("spacing","same_bank_power_separation"),
            ("old","guaranteed_quiet_gap_search_span"),("total","candidate_entry_to_ready_and_outgoing_retirement"),("H","H"))}
    a=json.loads((HERE/"a80_return_seat_results.json").read_text())["time_and_resources"]
    return {k:Q(a[v]) for k,v in (("q","quiet_epoch"),("spacing","true_same_bank_spacing"),
            ("old","stripe"),("total","total"),("H","H"))}


def source_margins(name,bodies):
    p=point(name)
    q,spacing=p["q"],p["spacing"]
    hosts,banks,slots=40,2,128
    n=banks*hosts
    # Numerical envelope tests, conditional on this assignment of real episodes.
    # One initial row per inherited body, one per prior fixed delivery slot,
    # and one left-boundary genuine new bank exposure per physical bank.
    body_count=n*bodies
    slot_count=n*slots
    rho=n/spacing
    def cost(profile):
        L=profile.first_sufficient_integer(q)
        require(L is not None and profile.verify(L,q) and not profile.verify(L-1,q),
                "Integer sufficient window not faithful to the affine test")
        total=p["total"]-p["old"]+L
        return dict(search=L,full_conditional_time=total,H_slack=p["H"]-total,
                    maintained_original_H=total<p["H"])
    count_only=Profile(body_count+slot_count+n,rho)
    all_events=cost(count_only)
    elapsed_one_by_one=cost(Profile.episodes(body_count+slot_count+n,rho,Q(3)))
    # An alternative source-local certificate can put the entire already
    # issued finite tail at the search cut inside ONE three-quantum hull.
    # The number of toggles strictly inside each accounted hull is unrestricted.
    joint=Profile(1,0,3,0).plus(Profile.episodes(body_count+n,rho,Q(3)))
    joined=cost(joint)
    require(all(x["maintained_original_H"] for x in (all_events,elapsed_one_by_one,joined)),
            "Original family horizon does not cover the example profile")
    sensitivity={}
    for per_epoch in range(1,5):
        probe=Profile.episodes(body_count+slot_count+n*per_epoch,per_epoch*rho,Q(3))
        threshold=probe.first_sufficient_integer(q)
        sensitivity[str(per_epoch)]=None if threshold is None else cost(probe)
    require(sensitivity["4"] is None and sensitivity["3"]["maintained_original_H"] == (name=="B"),
            "Family sensitivity at the fixed horizon changed")
    return dict(physical_banks=n,initial_body_rows=body_count,initial_delivery_slots=slot_count,
                episode_classes_per_new_bank=sensitivity,
                max_genuine_arrival_slope=rho,quiet_time=q,utilization=q*rho,original_H=p["H"],
                point_bursts=all_events,separate_three_q_hulls=elapsed_one_by_one,
                single_initial_tail_and_three_q_hulls=joined,
                endpoints="A committed issue and any late descendant belong to the same named hull only when its full causal reach fits.")


def arithmetic_checks():
    # All small integer-time closed intervals, up to three simultaneous or
    # overlapping reports, with rational interior candidate windows.
    cases=positive=0
    for L in range(1,7):
        dom=Interval(0,L)
        spans=[Interval(a,b) for a in range(-1,L+2) for b in range(a,L+2)]
        for n in range(4):
            for rows in combinations(spans,n):
                merged,gaps=union_and_gaps(dom,rows)
                volume=sum(i.width for i in merged)
                for q in (Q(1,2),Q(1)):
                    found=witness(dom,rows,q)
                    ample=L-volume>q*(len(merged)+1)
                    require(not ample or found is not None,"Pigeonhole conclusion failed")
                    require((found is not None)==any(g.width>q for g in gaps),"Incorrect gap sweep")
                    positive+=int(ample)
                    cases+=1
    equality=witness(Interval(0,3),[Interval(1,1),Interval(2,2)],1)
    require(equality is None,"Closed endpoints were discarded")
    arbitrary=[Interval(Q(i,100),Q(i,100)) for i in range(501)]
    require(witness(Interval(0,5),arbitrary,Q(1,50)) is None,"Zero busy time bought a free interval")
    # More than one active component per retained physical row is fine if
    # the union, including every re-opening, lies in one certified hull.
    family=[Interval(0,Q(1,10)),Interval(Q(1,5),Q(1,2)),Interval(1,Q(6,5)),Interval(2,2)]
    require(witness(Interval(0,5),[Interval(0,2)],2) is not None
            and witness(Interval(0,5),family,2) is not None,"Enclosing hull lost its valid quiet gap")
    capped=Profile.episodes(2,Q(1,20),3)
    low=capped.first_sufficient_integer(4)
    require(low is not None and capped.verify(low,4) and not capped.verify(low-1,4),"Occupied-time threshold failed")
    require(Profile(1,Q(1,2)).first_sufficient_integer(2) is None,"Critical density passed a strict test")
    return dict(clipped_calendars_and_lengths=cases,sufficient_cases=positive,
                endpoint_equality_has_no_closed_unit_window=True,
                zero_duration_many_points_has_no_wide_gap=True,
                multiple_reopens_inside_one_accounted_hull=True,positive_duration_example_first_integer=low)


def serialize(v):
    if isinstance(v,Q):
        return str(v)
    if isinstance(v,dict):
        return {k:serialize(x) for k,x in v.items()}
    return v


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    inputs={n:sha256((HERE/n).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for n in
            ("QuietWindow.lean","QUIET-WINDOW.md","quiet_window.py","a80_return_seat_results.json","return_itinerary_results.json")}
    result=serialize(dict(inputs=inputs,A80=source_margins("A",80),B=source_margins("B",1),
                          partitions=arithmetic_checks(),source_hull_realization=False))
    text=json.dumps(result,sort_keys=True,indent=2)+"\n"
    path=HERE/"quiet_window_results.json"
    if args.write:
        path.write_text(text,encoding="utf-8",newline="\n")
    else:
        require(path.read_text(encoding="utf-8")==text,"Different quiet-window certificate")
    print("Verified finite closed-interval selection and both conditional source budgets")
