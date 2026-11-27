"""Authored authority scope with a real, pinned RWARE journal dependency."""
from contextlib import closing, redirect_stdout
from pathlib import Path
from itertools import product
import importlib.util
import io
import json
import sqlite3
import sys
import tempfile

# First argv is preserved for the pinned parent's worker launcher.
# Import the pre-existing receiver kernel via path and do not rewrite it.
def module(name, p):
    spec = importlib.util.spec_from_file_location(name, p)
    out = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(out)
    return out

base = Path(sys.argv[1])
# The pinned module runs its reference calibration on import. Keep its
# assertions, but isolate its stdout from this replay's canonical JSON.
with redirect_stdout(io.StringIO()) as smoke:
    owner = module("owner", base / "owner.py")
assert json.loads(smoke.getvalue())["verified_rejections"] == 3
receiver = module("cut_receiver", base / "cut_receiver.py")
journal = owner.journal
key, sibling = owner.KEY, "sibling:7"


def execute(root, phase, use_sibling, disclose, operative, clear, delegation):
    source, issuers = root / "A.db", root / "B.db"
    owner.init(source, True)
    if use_sibling:
        with closing(owner.open_station(source)) as src:
            res = journal.apply(src, sibling, owner.PAYLOAD, "none", "bundled")
        assert res["result"] == [1, 0]
    else:
        assert owner.run(source, 1, phase, True)["status"] == "silent"

    with closing(owner.open_station(source)) as src:
        # Local, named, repeatable observation of the exact result in one read
        # snapshot; the second read intentionally loses its key identity.
        src.execute("begin")
        exact = src.execute("select tick,result from receipt where intent=?",
                            (key,)).fetchone()
        anonymous = src.execute("select tick,result from log where tick=8").fetchone()
        src.rollback()
    assert (exact is not None) == (not use_sibling and phase == "after-commit")
    assert (anonymous is not None) == (use_sibling or phase == "after-commit")

    # B's receipt records its actual earlier input, not a later reconstruction.
    # Grant text is independent of which source row it observed.
    with closing(sqlite3.connect(issuers, isolation_level=None)) as b:
        b.executescript("""create table appointment(scope text primary key,
            issuer integer, observed_key text, observed_tick integer);
            create table grant_record(scope text primary key, actor text);
        """)
        b.execute("insert into appointment values('support-port',?,?,?)",
                  (delegation,key,exact[0] if exact else None))
        b.execute("""insert into grant_record select scope,'backup'
            from appointment where issuer=1 and scope='support-port'""")

    # Native state after eventual application of the original job cannot tell
    # whether B observed its receipt before recording the appointment.
    donor_retry=owner.run(source,1)
    assert donor_retry["status"] in ("cached","applied")
    if not use_sibling:
        assert donor_retry["result"] == [1,0]
    final_source=owner.state(source)
    if not use_sibling:
        assert final_source["tick"] == 8
    else:
        assert final_source["tick"] == 9

    with closing(sqlite3.connect(issuers)) as b:
        decision=b.execute("""select observed_tick is not null from appointment
                where scope=? and observed_key=?""",('support-port',key)).fetchone()
        assert decision is not None
        exact_dependency=bool(decision[0])
        can_act=b.execute("select * from grant_record").fetchone() is not None

    # Frozen summary excludes keyed old commit, and sink commit requires B.
    # Missing disclosure is not a negative observation by the issuer.
    # Cut counts are historical only: current native clearance is checked below.
    oldmask, frozen, need=(3,(0,2),(4,7))
    def local(d):
        graph=(0,1,2) if d else (0,0,2)
        return receiver.propagated(graph,oldmask,frozen,need)
    good=local(exact_dependency) if disclose else None
    exact_local=(not exact_dependency) if disclose else False
    assert (good is not None) == exact_local
    whole = not exact_dependency
    assert (local(exact_dependency) is not None) == whole
    status="unresolved" if not disclose else ("compatible" if good else "incompatible")

    # A separate consuming RWARE layout, with optional actual occupancy from
    # an earlier operation. Stock movement still determines the effect.
    port=journal.iso.make(journal.n,False)
    actor=port.agents[1]
    if not clear:
        old=port.agents[0]
        old.x, old.y=2,1
        port._recalc_grid()
    local_clear=all((a.x,a.y)!=(2,1) for a in port.agents)
    assert local_clear == bool(clear)
    if good and can_act and operative and local_clear:
        journal.n.step(port,[owner.A.NOOP.value,owner.A.FORWARD.value])
    moved=(actor.x,actor.y)==(2,1)
    assert moved == bool(exact_local and delegation and operative and clear)
    side=journal.iso.make(journal.n,False)
    journal.n.step(side,[owner.A.NOOP.value,owner.A.FORWARD.value])
    assert (side.agents[1].x,side.agents[1].y)==(2,1)
    return dict(phase=phase,sibling=use_sibling,disclosure=disclose,
        operative=operative,clear=clear,delegation=delegation,history=status,
        source_tick=final_source["tick"],native_source=final_source["native"],
        source_anonymous_tick8=bool(anonymous), named_edge=(exact_dependency if disclose else None),
        rescue_position=(actor.x,actor.y), rescue=moved, side_position=(2,1))


def sweep():
    out=[]
    for phase,sib in [('after-stage',0),('after-commit',0),('after-stage',1)]:
        for flags in product((0,1),repeat=4):
            with tempfile.TemporaryDirectory() as d:
                out.append(execute(Path(d),phase,sib,*flags))
    by={(r["phase"],r["sibling"],r["disclosure"],r["operative"],r["clear"],r["delegation"]):r for r in out}
    no,yes,sib=(by[(p,s,1,1,1,1)] for p,s in [('after-stage',0),('after-commit',0),('after-stage',1)])
    assert no["native_source"]==yes["native_source"]
    assert no["source_tick"]==yes["source_tick"]==8
    assert no["rescue"] and not yes["rescue"] and sib["rescue"]
    assert yes["source_anonymous_tick8"] and sib["source_anonymous_tick8"]
    return {"cases":out, "counts":{v:sum(r["history"]==v for r in out)
                for v in ('compatible','incompatible','unresolved')}}


if __name__=="__main__":
    print(json.dumps(sweep(),indent=2,sort_keys=True))
