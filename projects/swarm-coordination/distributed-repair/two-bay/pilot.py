"""Two independent custody jobs, one coupled bay assignment. Python 3.12."""
import argparse
from itertools import product
import json

MODES = (0,1)
# At the two reached modes, these are the handedness of the installed
# passive guides that map A's lever to the physical bay. B's rail is direct.
LAYOUTS = {"base": (0,0), "local": (1,1), "coupling": (0,1)}
PHYSICAL_BAYS = ("near","far")


def enact(mode, layout, a, b, reserve=False):
    """The local views are not the complete shared-world record."""
    trace = [(0,"A_still_supports_its_own_load","A"),
             (0,"B_still_supports_its_own_load","B"),
             (1,"fixture_reaches_alignment",mode),
             (1,"A_local_view","own_load_held"),
             (1,"B_local_view",mode),
             (2,"simultaneous_commit",{"A":a,"B":b})]
    guide = PHYSICAL_BAYS[::-1] if layout[mode] else PHYSICAL_BAYS
    incoming = {"A": guide[a] if type(a) is int else None,
                "B": PHYSICAL_BAYS[b] if type(b) is int else
                     "reserve" if b=="reserve" and reserve else None}
    trace.append((2,"requested_actual_bays",incoming))
    both = all(incoming.values()) and len(set(incoming.values())) == 2
    # Fail closed on conflict: actual custody releases only if two
    # distinct sockets can accept both ongoing loads together.
    if both:
        trace.extend((3,"bay_accepts_load",(job,bay)) for job,bay in incoming.items())
    else:
        trace.append((3,"old_supports_continue",None))
    return dict(safe=True, service=bool(both), trace=trace)


def options(reserve):
    return (0,1,"wait","reserve") if reserve else (0,1,"wait")


def brute(layout,reserve=False):
    return {(a,bs) for a in (0,1,"wait") for bs in product(options(reserve),repeat=2)
            if all(enact(m,layout,a,bs[m],reserve)["service"] for m in MODES)}


def primitive_rows(layout,reserve=False):
    # Independent two-factor account: no overlap of physical bay positions.
    return {m:{(a,b) for a,b in product((0,1),options(reserve))
               if (b=="reserve" and reserve) or (type(b) is int and b != (a ^ layout[m]))}
            for m in MODES}


def direct_cached(layout,reserve=False):
    factors=primitive_rows(layout,reserve)
    # The same upstream policy entry a occurs in each factor; eliminate it
    # after the join. Retain both B observations together, not unary sets.
    return {(a,(b0,b1)) for a,b0 in factors[0] for other,b1 in factors[1] if a==other}


def contextual(layout,reserve=False):
    # Keep each reached branch and its actual pair of actions. The B
    # policy rows come from the same shared information section for A.
    worlds=[]
    for m in MODES:
        support = {(a,b) for a,b in product((0,1,"wait"),options(reserve))
                  if enact(m,layout,a,b,reserve)["service"]}
        worlds.append(support)
    return {(a,bs) for a in (0,1,"wait") for bs in product(options(reserve),repeat=2)
            if all((a,bs[m]) in worlds[m] for m in MODES)}


def show(rows):
    return [(a,list(bs)) for a,bs in sorted(rows,key=str)]


def general_cache():
    checked={}
    for m in range(1,7):
        binary=list(product((0,1),repeat=m))
        distinct=set()
        for guide in binary:
            projected={b for b in binary if any(all(b[i] != (a ^ guide[i]) for i in range(m)) for a in (0,1))}
            assert projected=={guide,tuple(1-x for x in guide)}
            assert all({b[i] for b in projected}=={0,1} for i in range(m))
            assert min(map(sum,projected)) == min(sum(guide),m-sum(guide))
            distinct.add(frozenset(projected))
        assert len(distinct)==2**(m-1)
        checked[m]=len(distinct)
    return checked


def check():
    allrows={}
    for name,layout in LAYOUTS.items():
        full=brute(layout)
        assert full==direct_cached(layout)==contextual(layout)
        assert len(full)==2
        allrows[name]=full
    bproj={key:{bs for a,bs in rel} for key,rel in allrows.items()}
    E={(0,0),(1,1)}
    O={(0,1),(1,0)}
    assert bproj=={"base":E,"local":E,"coupling":O}
    assert all({bs[i] for bs in bproj[k]}=={0,1} for i in MODES for k in LAYOUTS)
    old=(0,0)
    aold,= [a for a,bs in allrows["base"] if bs==old]
    anew,= [a for a,bs in allrows["local"] if bs==old]
    assert aold != anew
    assert not any(bs==old for a,bs in allrows["coupling"])
    cache = frozenset(bproj["base"])
    reuse = {k: frozenset(bproj[k]) == cache for k in ("local","coupling")}
    assert reuse == {"local":True,"coupling":False}
    assert (old in cache) == (old in bproj["local"]) and old not in bproj["coupling"]
    # Which B coordinate moves is a choice. At least one must move and
    # each can stay fixed in some viable repair.
    repaired_b={bs for a,bs in allrows["coupling"] if a==aold}
    assert len(repaired_b)==1
    assert min(sum(bs[i]!=old[i] for i in MODES) for bs in O)==1
    assert all(any(bs[i]==old[i] for bs in O) for i in MODES)
    assert all(enact(m,LAYOUTS["coupling"],"wait","wait")["safe"]
               and not enact(m,LAYOUTS["coupling"],"wait","wait")["service"] for m in MODES)
    assert all(("reserve","reserve") in {bs for a,bs in brute(l,True)} for l in LAYOUTS.values())
    assert all(direct_cached(l,True)==brute(l,True)==contextual(l,True) for l in LAYOUTS.values())
    runs={key:[enact(m,LAYOUTS[key],a,bs[m]) for m in MODES for a,bs in sorted(rel)]
          for key,rel in allrows.items()}
    diagnostics={key:[enact(m,LAYOUTS[key],a,0) for a in (0,1) for m in MODES]
                 for key in LAYOUTS}
    return dict(reuse_B_membership_if_same_projection=reuse,mask_generalization=general_cache(),policies={key:show(rel) for key,rel in allrows.items()},
                projection_B={key:sorted(rel) for key,rel in bproj.items()},
                removed=sorted(E-O),added=sorted(O-E),local_policy_reused=old,
                local_change_A=[aold,anew], traces=runs, old_B_diagnostics=diagnostics)


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--json",action="store_true")
    report=check()
    print(json.dumps(report,indent=2,sort_keys=True) if p.parse_args().json else report["policies"])
