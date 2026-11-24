"""Finite fork relief and local-policy checking. Python 3.12."""
from fractions import Fraction
from itertools import product
import argparse
import json

ACTIONS = ("left", "right", "wait")
FULL = tuple(product((0,1),repeat=2))
DIAGONAL = ((0,0),(1,1))
ANTI = ((0,1),(1,0))
# Schedule times are integer quarters of a tick. All hops take positive time.
OBSERVED, DECIDE, DEADLINE = 4,8,12


def reached(x,y,durations):
    """Run the finite prefix. x is root orientation; y is distal occupied lane."""
    assert x in (0,1) and y in (0,1)
    assert len(durations)==2 and all(d > 0 for d in durations)
    event = [(0,"place_loads_on_both_old_supports",None),
             (0,"root_observes_keyed_crossover",x)]
    # Both old supports remain until physically replaced. At 1 one load is
    # witnessed settled on its fixed rack, leaving the other still live.
    distal = [True,True]
    distal[1-y] = False
    event.extend([(4,"rack_receipt_discharges_distal_lane",1-y),
                  (4,"distal_fixture_samples_live_lane",y),
                  (4,"distal_fixture_issues_receipt",y)])
    t = OBSERVED + durations[0]
    event.append((t,"relay_receives_and_forwards",y))
    final = t + durations[1]
    event.append((final,"root_receipt",y))
    # A keyed crossover reverses the two alignments iff x is set.
    routed = distal[::-1] if x else distal[:]
    current_observation = (x,y,final) if final <= DECIDE else (x,None,None)
    return event,routed,current_observation


def run(x,y,durations,action):
    ev,live,view = reached(x,y,durations)
    ev.append((DECIDE,"commit_root_carriage",action))
    if action != "wait":
        j = ACTIONS.index(action)
        # A move to an already discharged branch doesn't destroy custody
        # elsewhere; it wastes the only available root-carriage movement.
        if live[j]:
            live[j] = False
            ev.append((DEADLINE,"accept_support_and_clear_old_carrier",action))
        else:
            ev.append((DEADLINE,"selected_branch_had_already_settled",action))
    done = not any(live)
    ev.append((DEADLINE,"relief_met" if done else "relief_missed",None))
    return dict(view=view, safe=True, service=done, trace=sorted(ev,key=lambda e:e[0]))


def projected(rows,durations):
    buckets = {}
    for x,y in rows:
        choices = {a for a in ACTIONS if run(x,y,durations,a)["service"]}
        o = reached(x,y,durations)[2]
        assert len(choices)==1
        buckets.setdefault(o,set(ACTIONS)).intersection_update(choices)
    return buckets


def direct(rows,durations):
    """Exhaustively try fixed policies H(view), independent of simulator."""
    worlds = []
    for x,y in rows:
        arrival = 4 + sum(durations)
        o = (x,y,arrival) if arrival <= 8 else (x,None,None)
        required = "left" if x == y else "right"
        worlds.append((o,required))
    keys = sorted({o for o,a in worlds},key=str)
    return [{k:a for k,a in zip(keys,assignment)}
            for assignment in product(ACTIONS,repeat=len(keys))
            if all(assignment[keys.index(o)]==a for o,a in worlds)]


def direct_factored(rows,durations):
    """Direct incremental contract: meet action factors per actual local key."""
    arrival = OBSERVED + sum(durations)
    relation = {}
    for x,y in rows:
        key = (x,y,arrival) if arrival <= DECIDE else (x,None,None)
        required = ("left","right")[x ^ y]
        relation[key] = relation.get(key,set(ACTIONS)) & {required}
    return relation


def separator(signs):
    """Schematic: eliminate one shared policy choice over both rows."""
    return {(a0,a1) for a0,a1,z in product((0,1), repeat=3)
            if (a0 ^ z,a1 ^ z) == signs}


def contextual_carrier(rows):
    """Exact finite bookkeeping carrier. Keep off-support raw tuples zero."""
    q = {(x,y): Fraction(int((x,y) in rows),len(rows)) for x,y in FULL}
    assert sum(q.values())==1
    marg_x = tuple(sum(q[x,y] for y in (0,1)) for x in (0,1))
    marg_y = tuple(sum(q[x,y] for x in (0,1)) for y in (0,1))
    # Disintegrate and reassemble on the root's keyed alignment.
    conditionals = {(x,y): q[x,y]/marg_x[x] if marg_x[x] else Fraction() for x,y in FULL}
    assert {(x,y):marg_x[x]*conditionals[x,y] for x,y in FULL} == q
    support = tuple(w for w,p in q.items() if p > 0)
    assert set(support) == set(rows)
    return support,(marg_x,marg_y)


def solved(rows,durations):
    support,_ = contextual_carrier(rows)
    projection = projected(support,durations)
    reference = direct_factored(rows,durations)
    assert projection == reference
    exact = direct(rows,durations)
    if all(choices for choices in projection.values()):
        assert len(exact)==1 and exact[0] == {k:next(iter(v)) for k,v in projection.items()}
    else:
        assert exact == []
    return dict(winning=bool(exact),projection=[
        [list(k),sorted(v)] for k,v in sorted(projection.items(),key=lambda item:str(item[0]))])


def main():
    on = (1,3)
    same = (3,1)
    late = (2,6)
    one = (2,3)
    assert reached(0,0,late)[2]==reached(0,1,late)[2]
    assert solved(((0,0),(0,1)),late)["projection"] == [[[0,None,None],[]]]
    controls = {}
    for name,ds in (("on_time",on),("late",late),("one_quarter_late",one)):
        controls[name] = solved(FULL,ds)
        assert controls[name]["winning"] == (name=="on_time")
    assert solved(FULL,on)==solved(FULL,same)
    assert all(run(x,y,ds,"wait")["safe"] and not run(x,y,ds,"wait")["service"]
               for x,y in FULL for ds in (on,same,late,one))
    assert OBSERVED + sum(late) == DECIDE + 4
    # The receipt and its action projection are unchanged although the
    # actual relay event occurs at a different internal tick.
    assert reached(0,0,on)[0]!=reached(0,0,same)[0]
    d,m = contextual_carrier(DIAGONAL)
    a,m2 = contextual_carrier(ANTI)
    assert m == m2 == ((Fraction(1,2),)*2,)*2
    diag,anti = solved(d,late),solved(a,late)
    assert diag["winning"] and anti["winning"] and diag!=anti
    assert all(solved((world,),late)["winning"] for world in FULL)
    def differing(old_projection,new_projection):
        a,b = (dict((tuple(key),value) for key,value in q["projection"])
               for q in (old_projection,new_projection))
        return sorted((k for k in set(a)|set(b) if a.get(k)!=b.get(k)),key=str)
    coupling_changes = differing(diag,anti)
    private_changes = differing(solved(FULL,on),solved(FULL,same))
    assert coupling_changes == [(0,None,None),(1,None,None)] and private_changes == []
    equal,opposite = separator((0,0)),separator((0,1))
    assert equal == {(0,0),(1,1)} and opposite == {(0,1),(1,0)}
    assert all({row[i] for row in r} == {0,1} for i in (0,1) for r in (equal,opposite))
    return dict(timing=controls,schematic_separator={"equal":sorted(equal),"opposite":sorted(opposite)},
                cache_changed_rows=dict(relay=private_changes,coupling=coupling_changes),
                support_laws=dict(diagonal=diag,anti=anti),
                controls={name:[dict(branch=[x,y],action=act,**run(x,y,ds,act))
                                for x,y in FULL for act in ACTIONS]
                          for name,ds in (("on_time",on),("late",late))})


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--json",action="store_true")
    report=main()
    if p.parse_args().json:
        print(json.dumps(report,sort_keys=True,indent=2))
    else:
        print({k:v["winning"] for k,v in report["timing"].items()})
        print(report["support_laws"])
