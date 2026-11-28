#!/usr/bin/env python3
"""Project compiled source calls into the frozen shared admission core."""
from csv import DictReader
from hashlib import sha1
from itertools import product
from pathlib import Path
from subprocess import check_output
import argparse
import json
import sys

HERE = Path(__file__).resolve().parent
CORE_HASH = "687bf1250c6725992b6de696d0781d7948b4a89e"

OPTIONS = {
    "primary_plain": (0,1,0),
    "primary_early": (1,1,0),
    "primary_inline": (2,1,0),
    "backup": (0,0,1),
}
# Source returns raw actuator dispatches. The model pays the named old duty
# at its first matching dispatch; subsequent authorized old force maintain
# operations are not duplicate settlements. New service goes to exactly one
# receiver. No plant velocity or motion observation is synthesized.
DUE = {"old-effort":1, "new-velocity":1, "independent":1}

def native_table():
    raw=check_output([sys.executable,str(HERE/"native.py")],text=True)
    table={}
    late=[]
    for record in DictReader(raw.splitlines()):
        record={k:int(v) for k,v in record.items()}
        if record["late"]:
            late.append(record)
            continue
        k=tuple(record[n] for n in ("prior","writer","release","installP","backup"))
        assert k not in table
        table[k]=record
    assert len(late)==1
    assert late[0]["ack"]==1 and late[0]["pvel"]==0 and late[0]["pforce"]==1
    return table

def world_row(core,table,past,writer,q_ready,has_gate):
    def E(at,order,paid=()):
        return core.Event(at,order,paid=tuple(paid))
    case=table[past,writer,0,0,0]
    options={}
    for name,(release,install,backup) in OPTIONS.items():
        if name=="backup" and not q_ready: continue
        if name in ("primary_inline","primary_early") and not has_gate: continue
        packet=table[past,writer,release,install,backup]
        claims=[]
        if not case["past"] and packet["pforce"]: claims.append("old-effort")
        if packet["pvel"]: claims.append("new-velocity")
        if packet["qvel"]: claims.append("new-velocity")
        if packet["side"]: claims.append("independent")
        options[name]=(E(1,1,claims),)
    events=(E(0,0,("old-effort",)),) if case["past"] else ()
    return core.Row((),frozenset(),events,options)

def independent_formula(p,w,q,g):
    # Boolean source control model, not learned from the compiled trace.
    return set(name for name,ok in (
        ("primary_plain",False),
        ("primary_early",p and not w and g),
        ("primary_inline",p and g),
        ("backup",q and (p or w)),
    ) if ok)

def choose(core,rows,view):
    a=core.admitted(rows,"replacement",1,DUE,OPTIONS)
    return set(a[view])

def add_receipt(core,row,paid,arrives):
    # Positive job-specific evidence from the prior source record; modeled
    # channel can hide or delay it. No negative assertion is fabricated.
    r=((arrives,"replacement",("old-effort","P",0)),) if paid else ()
    return core.Row(r,row.facts,row.events,row.options)

def main():
    arg=argparse.ArgumentParser()
    arg.add_argument("--core",type=Path,default=(HERE/"core.py" if (HERE/"core.py").is_file()
                    else HERE.parents[1]/"core.py"))
    core_path=arg.parse_args().core.resolve()
    buf=core_path.read_bytes()
    actual=sha1(f"blob {len(buf)}\0".encode()+buf).hexdigest()
    assert actual==CORE_HASH,(actual,CORE_HASH)
    sys.path.insert(0,str(core_path.parent))
    import core
    assert Path(core.__file__).resolve()==core_path
    table=native_table()
    assert len(table)==48
    cases=list(product((0,1),repeat=4))
    rows=[]
    for p,w,q,g in cases:
        row=world_row(core,table,p,w,q,g)
        exact={n for n in OPTIONS if core.check(row,n,1,DUE)}
        assert exact==independent_formula(p,w,q,g),(p,w,q,g,exact)
        rows.append(row)
    # Exact case inclusion changes without exposing the array index.
    # These are model envelopes, not a claim every envelope is native or
    # known to a controller. Per concrete world, compare all native variants.
    checked=0
    for mask in range(1,1<<len(rows)):
        xs=[i for i in range(len(rows)) if mask>>i&1]
        ans=choose(core,[rows[i] for i in xs],())
        expected=set(OPTIONS)
        for i in xs: expected.intersection_update(independent_formula(*cases[i]))
        assert ans==expected
        checked+=1
    def get(prior,writer,release,p,backup):
        return table[prior,writer,release,p,backup]
    stale=get(1,1,1,1,0); anchored=get(1,1,2,1,0)
    assert stale["ack"]==anchored["ack"]==1
    assert (stale["pvel"],anchored["pvel"])==(0,1)
    # Same local observation under late/no report: only the independent
    # standby serves both histories. Timely report also makes P usable in
    # the paid history and the old path remains live in the pending one.
    no_receipt=[world_row(core,table,p,1,1,1) for p in (0,1)]
    assert choose(core,no_receipt,())=={"backup"}
    tagged=[add_receipt(core,r,p,1) for p,r in enumerate(no_receipt)]
    paid_obs=((1,("old-effort","P",0)),)
    assert choose(core,tagged,())=={"backup"}
    assert choose(core,tagged,paid_obs)=={"primary_inline","backup"}
    if_late=[add_receipt(core,r,p,2) for p,r in enumerate(no_receipt)]
    assert choose(core,if_late,())=={"backup"}
    assert choose(core,[world_row(core,table,p,1,0,1) for p in (0,1)],())==set()
    # Ordinary primary-only and eager drain comparisons, both with the
    # same cut and evidence when available. The eager action discards old
    # pending work; selecting the fallback protects it. Equally informed
    # direct admission above ties in every envelope.
    disrupted=get(0,1,2,1,0)
    recovered=get(0,1,0,0,1)
    assert not disrupted["pforce"] and disrupted["pvel"] and disrupted["side"]
    assert recovered["pforce"] and recovered["qvel"] and recovered["side"]
    print(json.dumps(dict(native_rows=len(table),envelopes=checked,
                          additional_late_writer_control=1,early_ack=stale["ack"],early_primary_dispatch=stale["pvel"],
                          inline_primary_dispatch=anchored["pvel"],
                          no_report=sorted(choose(core,no_receipt,())),
                          timely_paid_report=sorted(choose(core,tagged,paid_obs)),
                          pending_stock_old_and_backup=[recovered["pforce"],recovered["qvel"]],
                          independent_both=[disrupted["side"],recovered["side"]]),sort_keys=True))

if __name__=="__main__":
    main()
