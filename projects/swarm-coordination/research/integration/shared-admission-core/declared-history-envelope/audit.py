"""Admission envelope audit for two held-in selected-source studies.

Validates pinned replay outputs, not source completeness in an unmodeled plant.
A point key records experiment history; it is not visible to the controller.
"""
from itertools import product
from copy import deepcopy
from pathlib import Path
import hashlib
import json
import sys


class EnvelopeError(ValueError):
    pass


def exact_domain(expected, entries):
    rows = {}
    for key, row in entries:
        if key in rows:
            raise EnvelopeError("duplicate history")
        rows[key] = row
    unexpected = rows.keys() - expected
    missing = expected - rows.keys()
    if unexpected or missing:
        raise EnvelopeError("missing or extra history")
    return rows


def radio_key(r):
    return tuple(r[k] for k in ("mode", "notice", "debit", "backup_P", "old_Q"))


def warehouse_key(r):
    return tuple(r[k] for k in ("lost", "notice", "cap", "optional_required"))


def radio_expected():
    return set(product(("Q", "P"), (None, 7, 8), (33, 34), (0, 1), (0, 1)))


def warehouse_expected():
    return set(product((None, "B", "C"), (None, 6, 7), range(2, 7), (False, True)))


def radio_effect(key, row):
    s, notice, debit, p, q = key
    native = row["native"]
    callbacks = native["radio"]
    observed = [x for x in callbacks if x[0] == 7 and x[1:6] ==
                ["Base", "preq", 1, 1, True]]
    assert len(observed) == int(notice == 7)
    # Preparation requires named authorization AND observed callback.
    admissible = bool(observed and (q if s == "Q" else p and debit <= 33))
    matching = [x for x in callbacks if x[0:6] == [8, s, "owed", 173, 173, True]]
    settled = native["apply"] == 8 and native["result"] == {
        "status": "cached", "tick": 8, "result": [1, 0]}
    assert settled == admissible and len(matching) == int(settled)
    assert native["side"] == 2
    assert native["charged"] == sum(x[4] for x in callbacks) + 2
    if settled:
        target = "preq" if s == "Q" else "preP"
        assert sum(x == [7, "Base", target, 2, 2, True] for x in callbacks) == 1
        assert native["selection"] == [s, 10 if s == "Q" else 7]
    else:
        assert native["apply"] is None and native["result"] is None
        assert native["selection"] is None
    return settled


def warehouse_effect(key, row):
    loss, notice, cap, required = key
    # The read's latency and trust are fixture assumptions. Class acceptance
    # and Home unloading, not the ROBOTFAULT transport flag, are effects.
    b, c = (loss == "B", loss == "C") if notice == 6 else (True, True)
    paid = 2+2*b+c+required <= cap
    assert row["side_return"] is True
    if paid:
        opt = 2+2*b+c+1 <= cap
        assert row["chosen"] == [int(b), int(c), int(opt)]
        assert row["paid_old"] == [[1, 9]]
        assert row["accepted"] == ["item"+str(i) for i in range(7, 2, -1)]
        assert row["picked"] == 2+2*b+c+opt
        assert row["optional_staged"] is opt
    else:
        assert row["chosen"] is None and row["paid_old"] == []
        assert row["accepted"] == [] and row["picked"] == 0
        assert row["optional_staged"] is False
    return paid


def mutants(domain, rows):
    counts = {"single_omission": 0, "duplicate": 0, "foreign": 0,
              "equal_count_substitution": 0}
    entries = list(rows.items())
    assert exact_domain(domain, reversed(entries)) == rows
    def fails(trial, label):
        try:
            exact_domain(domain, trial)
        except EnvelopeError:
            counts[label] += 1
        else:
            raise AssertionError(label)
    for i, entry in enumerate(entries):
        rest = entries[:i]+entries[i+1:]
        fails(rest, "single_omission")
        fails(entries+[entry], "duplicate")
        foreign = (("foreign",)+entry[0], entry[1])
        fails(entries+[foreign], "foreign")
        fails(rest+[foreign], "equal_count_substitution")
    return counts


def cut_witnesses(core, radio, warehouse):
    table = {}
    for label, cut, actor, dues, cases, adverse, action in (
        ("radio", 7, "entry", radio.DUES,
         {s:radio.row(s,None,33,{"Q","P"}) for s in ("Q","P")}, "P", ("Q",10)),
        ("warehouse", 6, "dispatcher", warehouse.dues,
         {s:warehouse.row(s,None,4,False) for s in (None,"B","C")}, "B", (0,1,0)),
    ):
        # These actual cases have common menus; consequences can differ in
        # general. The join only certifies existence for each coarse label.
        labelset = (label,)
        def f(r):
            return core.Fragment(labelset, r.receipts, r.facts, r.events)
        options = next(iter(cases.values())).options
        assert all(r.options == options for r in cases.values())
        right = [core.Fragment(labelset, (), frozenset(), ())]
        query = lambda left: core.admitted(core.join((f(r) for r in left), right,
                                            {action:options[action]}),
                                            actor, cut, dues, (action,))[()]
        rest = {k:r for k,r in cases.items() if k != adverse}
        assert query(cases.values()) == ()
        assert query(rest.values()) == (action,)
        exact_domain(set(cases), cases.items())
        try:
            exact_domain(set(cases), rest.items())
        except EnvelopeError:
            pass
        else:
            raise AssertionError("missing adverse history")
        table[label] = {"full": "refuse", "coarse_join_after_omission": "admit",
                        "sealed_after_omission": "unresolved"}
    return table


def main():
    root = Path(sys.argv[1])
    pins = json.loads(Path(__file__).with_name("PINS.json").read_text())
    for name, pin in pins.items():
        p = root/name
        assert hashlib.sha256(p.read_bytes()).hexdigest() == pin["sha256"], name
    sys.path.insert(0,str(root))
    import core
    import radio
    import warehouse
    vals = {}
    for name, doc, field, spec, key, check in (
        ("radio", "radio.json", "native", radio_expected, radio_key, radio_effect),
        ("warehouse", "warehouse.json", "native_cases", warehouse_expected, warehouse_key, warehouse_effect),
    ):
        domain = spec()
        rows = json.loads((root/doc).read_text())[field]
        mapped = exact_domain(domain, ((key(r),r) for r in rows))
        successes = sum(check(k,r) for k,r in mapped.items())
        vals[name] = {"histories":len(domain), "settled":successes,
                      "side_work":len(domain), "defects_rejected":mutants(domain,mapped)}
    r = next(v for v in json.loads((root/"radio.json").read_text())["native"]
             if v["native"]["apply"] == 8)
    w = next(v for v in json.loads((root/"warehouse.json").read_text())["native_cases"]
             if v["paid_old"])
    for row,key,check,edit in (
        (r,radio_key,radio_effect,lambda v:v["native"].update(result=None)),
        (r,radio_key,radio_effect,lambda v:v["native"].update(side=1)),
        (w,warehouse_key,warehouse_effect,lambda v:v["accepted"].pop()),
        (w,warehouse_key,warehouse_effect,lambda v:v.update(side_return=False)),
    ):
        altered = deepcopy(row)
        edit(altered)
        # Membership alone accepts a valid key with false effect fields.
        exact_domain({key(row)}, [(key(altered),altered)])
        try:
            check(key(altered),altered)
        except AssertionError:
            pass
        else:
            raise AssertionError("false effect")
    vals["false_effect_controls_rejected"] = 4
    vals["controller_witnesses"] = cut_witnesses(core,radio,warehouse)
    print(json.dumps(vals, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
