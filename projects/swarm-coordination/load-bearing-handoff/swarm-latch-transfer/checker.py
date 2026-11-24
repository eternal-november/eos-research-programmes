"""Frozen D transfer check, Python 3.12+, standard library only."""
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

PIN = "9331dd48c9468e8dac559bb0c8dbfac412b311c963645801af7b90f5d53fded7"
SLOTS = ("[1,1.5)", "[1.5,2)", "[2,2.5)", "[2.5,3)", "[3,3.5)", "[3.5,4)")
FACTOR = {(p,l): (2,2,4,4,0,0) if p else (1,1,0,0,0,0)
          for p in (False,True) for l in (False,True)}


def require(ok, why):
    if not ok:
        raise ValueError(why)


def record(d, keys):
    require(isinstance(d, dict) and set(d) == set(keys.split()), f"Expected fields {keys}")


def name(s):
    return isinstance(s, str) and bool(s.strip())


def local_machine(doc):
    record(doc, "initial transitions worlds")
    require(name(doc["initial"]), "Invalid initial state")
    table = {}
    for row in doc["transitions"]:
        record(row, "state symbol next demand")
        key = (row["state"], row["symbol"])
        require(all(name(s) for s in (*key, row["next"])), "Invalid machine vocabulary")
        units = row["demand"]
        require(type(units) is int and 0 <= units <= 4, "Invalid demand")
        require(key not in table, "Duplicate transition")
        table[key] = (row["next"], units)
    require(bool(table), "Empty machine")
    branches = {}
    seen = set()
    for row in doc["worlds"]:
        record(row, "id partial lost symbols provenance")
        i,p,l = row["id"],row["partial"],row["lost"]
        require(name(i) and i not in branches and name(row["provenance"]), "Invalid ID or provenance")
        require(type(p) is bool and type(l) is bool, "Invalid handoff branch")
        require(isinstance(row["symbols"], list) and len(row["symbols"]) == len(SLOTS)
                and all(name(x) for x in row["symbols"]), "Expected one local symbol per slot")
        demand,states = [],[doc["initial"]]
        for x in row["symbols"]:
            k = (states[-1],x)
            require(k in table, f"Missing transition {k}")
            state,units = table[k]
            states.append(state)
            demand.append(units)
        seen.add((p,l))
        branches[i] = ((p,l), tuple(demand), states)
    require(seen == set(FACTOR), "All four latch/report branches required")
    return branches


def direct(branches):
    failures = {}
    for i,(w,d,_) in branches.items():
        if sum(d[:2]) < 4 or sum(d[4:]) < 2:
            failures.setdefault(i, []).append("D")
        for j,(h,u) in enumerate(zip(FACTOR[w],d)):
            if h+u > 4:
                failures.setdefault(i, []).append(SLOTS[j])
    return failures


def contextual(branches):
    # Identity coefficients and no body map. Restrict raw separate factors
    # along the EXACT declared joint occurrence relation, not the product of
    # observations, D runs, or branch marginals.
    hraw = {w: dict(zip(SLOTS,h)) for w,h in FACTOR.items()}
    draw = {i: dict(zip(SLOTS,d)) for i,(_,d,_) in branches.items()}
    # Uniform mass on the declared source-world IDs is a bookkeeping law;
    # only support is scored. u is the common latch/report phase. Hraw has
    # one row per u; Draw gives each admitted D occurrence a unique ID.
    unit = Fraction(1,len(branches))
    generated = {(w,w,i): unit for i,(w,_,_) in branches.items()}  # (u,Hraw,Draw)
    raw_carrier = {(w,i): sum((q for (_,h,d),q in generated.items() if h==w and d==i), Fraction())
                   for w in hraw for i in draw}
    assert sum(raw_carrier.values()) == 1
    h_marginal = {w: sum(raw_carrier[w,i] for i in draw) for w in hraw}
    d_marginal = {i: sum(raw_carrier[w,i] for w in hraw) for i in draw}
    assert h_marginal == {w: sum((q for (u,_,_),q in generated.items() if u==w), Fraction())
                          for w in hraw}
    assert all(q == unit for q in d_marginal.values())
    # Restrict by actual common phase, then reassemble with its exact mass.
    conditioned = {w: {i: raw_carrier[w,i]/h_marginal[w] for i in draw} for w in hraw}
    assert all(sum(rows.values()) == 1 for rows in conditioned.values())
    assert {(w,i): h_marginal[w]*conditioned[w][i] for w in hraw for i in draw} == raw_carrier
    assert {(w,w,i): q for (w,i),q in raw_carrier.items() if q} == generated
    failure = {}
    for (w,i),weight in raw_carrier.items():
        if weight == 0:
            continue  # Off-support raw entry stays zero; no certificate obligation.
        p,q = hraw[w], draw[i]
        if q[SLOTS[0]]+q[SLOTS[1]] < 4 or q[SLOTS[-2]]+q[SLOTS[-1]] < 2:
            failure.setdefault(i, []).append("D")
        for s in SLOTS:
            if not p[s] <= 4-q[s]:
                failure.setdefault(i, []).append(s)
    return failure


def literal(branches):
    # Place H into lowest slots and enumerate injections of D units into
    # the remaining places. Independent of add/subtract inequalities.
    from itertools import combinations
    failure = {}
    for i,(w,d,_) in branches.items():
        work = [s for s,u in enumerate(d) for _ in range(u)]
        if sum(s in (0,1) for s in work) < 4 or sum(s in (4,5) for s in work) < 2:
            failure.setdefault(i, []).append("D")
        template = [1,1,0,0,0,0] if not w[0] else [2,2,4,4,0,0]
        for j,u in enumerate(d):
            remainder = set(range(4)).difference(range(template[j]))
            if next(combinations(remainder,u), None) is None:
                failure.setdefault(i, []).append(SLOTS[j])
    return failure


def evaluate(doc):
    branches = local_machine(doc)
    a,b,c = direct(branches),contextual(branches),literal(branches)
    assert a == b == c, (a,b,c)
    return {"pass": not a, "failure": a,
            "branches": {i: {"latch_report": w, "D": d, "D_states": states}
                         for i,(w,d,states) in branches.items()}}


def verify_pilot(path):
    require(hashlib.sha256(path.read_bytes()).hexdigest() == PIN,"Pinned H source hash mismatch")
    spec = importlib.util.spec_from_file_location("pinned_pilot",path)
    old = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = old
    spec.loader.exec_module(old)
    for w in old.worlds():
        r = old.finish(w,"probe","cradle" if w.partial else "release")
        assert r["safe"] and r["service"] and r["d_service"]
        x, = [e[2]["cradle"] for e in r["trace"] if e[1] == "probe-load-share"]
        y = sum(e[2]["cradle"] for e in r["trace"] if e[1] == "cradle-takes-load")
        assert FACTOR[w.partial,w.lost] == (x,x,y,y,0,0)


def main():
    folder = Path(__file__).resolve().parent
    verify_pilot(folder.parent / "swarm-latch-pilot" / "pilot.py")
    doc = json.loads((folder / "baseline.json").read_text())
    original = evaluate(doc)
    assert original["pass"] and all(tuple(r["D"]) == (2,2,0,0,1,1) for r in original["branches"].values())
    # Previously checked probe overload: use D=3 in both early half-slots.
    for edge in doc["transitions"]:
        if edge["demand"] == 2:
            edge["demand"] = 3
    stress = evaluate(doc)
    assert list(stress["failure"]) == ["partial-report","partial-missing"]
    require(len(sys.argv) <= 2, "Usage: checker.py [machine.json]")
    payload = evaluate(json.loads(Path(sys.argv[1]).read_text())) if len(sys.argv)==2 else {
        "original": original, "known_overload": stress}
    print(json.dumps(payload,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
