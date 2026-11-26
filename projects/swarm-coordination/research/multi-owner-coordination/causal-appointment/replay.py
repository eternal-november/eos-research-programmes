"""Independent civil permit ledgers. No network, real robot, or service access."""
import itertools
import json
import sqlite3
import tempfile
from pathlib import Path


def db(path):
    c = sqlite3.connect(path, isolation_level=None)
    c.execute("PRAGMA journal_mode=WAL")
    return c


def run(root, late, disclose, permit, occupied, can_delegate):
    a = db(root / 'owner_a.db')
    b = db(root / 'owner_b.db')
    plant = db(root / 'plant.db')
    a.executescript("""CREATE TABLE rev(v INTEGER PRIMARY KEY, amend INTEGER);
    INSERT INTO rev VALUES(1,1);""")
    b.executescript("""CREATE TABLE appointment(v INTEGER PRIMARY KEY, crew TEXT,
          issue_power INTEGER, observed_a INTEGER);
    CREATE TABLE grants(job TEXT PRIMARY KEY, crew TEXT, source INTEGER);
    """)
    plant.executescript("""CREATE TABLE gate(access INTEGER);
    CREATE TABLE effects(job TEXT PRIMARY KEY, lane TEXT);
    CREATE TABLE position(crew TEXT PRIMARY KEY, site TEXT);
    INSERT INTO position VALUES ('crew','wait'),('old','shared'),('inspector','base');
    """)
    plant.execute("INSERT INTO gate VALUES(1)")
    if late:
        a.execute("INSERT INTO rev VALUES(2,0)")
    # B is entitled to appoint on its own ledger. For using the lift, A's
    # specific charter separately requires that the appointment carry a guard
    # against an enabling administration cut (not current operative access).
    observed, = a.execute("SELECT MAX(v) FROM rev").fetchone()
    b.execute("INSERT INTO appointment VALUES(1,'crew',?,?)",
              (can_delegate, observed))
    if not late:
        a.execute("INSERT INTO rev VALUES(2,0)")
    # Both exports genuinely describe their named historical versions.
    av, enabling = a.execute("SELECT v, amend FROM rev WHERE v=1").fetchone()
    bv, crew, power = b.execute("SELECT v, crew, issue_power FROM appointment").fetchone()
    view = [av, enabling, bv, crew, power]
    # No observer reads local B storage. B offers one named threshold and the
    # returned authentic answer is modeled, not cryptographically implemented.
    bit = None
    if disclose:
        bit, = b.execute("SELECT observed_a <= ? FROM appointment WHERE v=?",
                        (av, bv)).fetchone()
    verdict = {None:'unresolved', 0:'incompatible', 1:'compatible'}[bit]
    # Full-information baseline enumerates actual selectable authority prefixes.
    # The fixed-consent baseline ignores dependencies, not future issue power.
    allowed_a = [r[0] for r in a.execute("SELECT v FROM rev WHERE amend=1")]
    allowed_b = list(b.execute("SELECT v, observed_a FROM appointment WHERE crew='crew'"))
    exhaustive = any(v >= d for v in allowed_a for _, d in allowed_b)
    assert exhaustive == (not late)
    if disclose:
        assert (verdict == 'compatible') == exhaustive
    # A real second issuance on B, not a status bit or pre-issued fallback.
    cur = b.execute("""INSERT INTO grants
        SELECT 'rescue', crew, v FROM appointment
        WHERE v=? AND crew=? AND issue_power=1""", (bv, crew))
    issued = cur.rowcount == 1
    assert issued == bool(can_delegate)
    # Fixture locally serializes gate observation and effect; it does not
    # implement distributed atomicity or coordinate the owners' amendments.
    plant.execute("BEGIN IMMEDIATE")
    if not permit:
        plant.execute("UPDATE gate SET access=0")
    if not occupied:
        plant.execute("UPDATE position SET site='exit' WHERE crew='old'")
    plant.execute("COMMIT")
    plant.execute("BEGIN IMMEDIATE")
    current_access, old_load = plant.execute("""SELECT access,
        EXISTS(SELECT 1 FROM position WHERE crew='old' AND site='shared')
        FROM gate""").fetchone()
    if verdict == 'compatible' and issued and current_access and not old_load:
        plant.execute("UPDATE position SET site='shared' WHERE crew='crew'")
        plant.execute("INSERT INTO effects VALUES('rescue','shared')")
    plant.execute("UPDATE position SET site='other' WHERE crew='inspector'")
    plant.execute("INSERT INTO effects VALUES('inspection','other')")
    plant.execute("COMMIT")
    effect = list(plant.execute("SELECT * FROM effects ORDER BY job"))
    poses = dict(plant.execute("SELECT * FROM position ORDER BY crew"))
    assert (poses['old'] == 'shared') == bool(occupied)
    assert poses['inspector'] == 'other'
    actual = ['rescue', 'shared'] in [list(r) for r in effect]
    match = disclose and exhaustive and issued and permit and not occupied
    fixed_consent = issued and permit and not occupied
    assert actual == bool(match)
    assert ('inspection', 'other') in effect
    for c in (a, b, plant):
        c.close()
    return dict(late=late, disclosed=disclose, consuming_access=permit,
                old_load=occupied, issue_power=can_delegate, view=view,
                verdict=verdict, second_grant=issued, model_positions=poses, physical_effects=effect,
                baseline_fixed_consent=bool(fixed_consent), actual=actual)



def greatest_cut(allowed, floors):
    if not all(allowed):
        return None
    candidate = [max(a) for a in allowed]
    while True:
        change = False
        for i, vi in enumerate(candidate):
            feasible = [u for u in allowed[i] if u <= vi and
                        all(d <= t for d, t in zip(floors[i][u], candidate))]
            if not feasible:
                return None
            new = max(feasible)
            if new != vi:
                candidate[i] = new
                change = True
        if not change:
            return tuple(candidate)


def audit():
    """Causally generated vector bounds, incl. holes in permitted version sets."""
    import random
    rng = random.Random(826357)
    found = absent = hole = 0
    for _ in range(16384):
        n, m = 3, 5
        seq = [i for i in range(n) for _ in range(m - 1)]
        rng.shuffle(seq)
        floors = [[[0]*n] for _ in range(n)]
        for i in seq:
            last = floors[i][-1][:]
            for j in range(n):
                if i != j and rng.randrange(3) == 0:
                    # Incorporate the cause's entire causal past.
                    v = rng.randrange(len(floors[j]))
                    for k in range(n):
                        last[k] = max(last[k], floors[j][v][k])
                    last[j] = max(last[j], v)
            floors[i].append(last)
        allowed = [sorted(rng.sample(range(m), rng.randrange(1, m+1))) for _ in range(n)]
        hole += any(len(a) < a[-1] - a[0] + 1 for a in allowed)
        exact = [x for x in itertools.product(*allowed)
                 if all(all(d <= t for d, t in zip(floors[i][x[i]], x))
                        for i in range(n))]
        observed = greatest_cut(allowed, floors)
        if exact:
            found += 1
            expected = tuple(max(x[i] for x in exact) for i in range(n))
            assert expected in exact and observed == expected
        else:
            absent += 1
            assert observed is None
    return dict(satisfiable=found, infeasible=absent, with_holes=hole)


def main():
    cases = []
    for bits in itertools.product((0, 1), repeat=5):
        with tempfile.TemporaryDirectory() as p:
            cases.append(run(Path(p), *bits))
    outcomes = {v: sum(c['verdict'] == v for c in cases) for v in
                ('compatible', 'incompatible', 'unresolved')}
    assert outcomes == dict(compatible=8, incompatible=8, unresolved=16)
    assert sum(c['actual'] for c in cases) == 1
    by_key = {(c['late'], c['disclosed'], c['consuming_access'],
               c['old_load'], c['issue_power']): c for c in cases}
    good, bad = (by_key[(i, 1, 1, 0, 1)] for i in (0, 1))
    assert good['view'] == bad['view'] and good['actual'] and not bad['actual']
    assert bad['baseline_fixed_consent']
    assert by_key[(0, 0, 1, 0, 1)]['verdict'] == by_key[(1, 0, 1, 0, 1)]['verdict']
    print(json.dumps(dict(cases=cases, outcomes=outcomes, cut_audit=audit()), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
