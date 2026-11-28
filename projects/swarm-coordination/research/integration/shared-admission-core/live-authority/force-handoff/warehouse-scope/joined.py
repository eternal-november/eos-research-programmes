#!/usr/bin/env python3
"""Join actual selected warehouse transition with the pinned dispatch replay.

Layout and scope policy are authored. The only assumed live evidence is an
inline read of the named cells and (where declared) a prior dispatch receipt.
Do not interpret its offline enumeration as a robot observer or as Gazebo motion.
"""
import hashlib
import importlib.util
from itertools import product
import json
import os
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
PINNED=Path(os.environ.get("WAREHOUSE_PINS",HERE/"pinned"))
DISPATCH=HERE if (HERE/"core.py").is_file() else HERE.parent
CORE=HERE/"core.py" if (HERE/"core.py").is_file() else HERE.parents[2]/"core.py"
ISOLATOR="610a81b316a9b3538106387467c4e2f4437b28f4"

def blob(s):return hashlib.sha1(f"blob {len(s)}\0".encode()+s).hexdigest()

def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec)
    sys.modules[name]=m
    spec.loader.exec_module(m)
    return m

assert blob((PINNED/"isolated.py").read_bytes())==ISOLATOR
iso=load("warehouse_source",PINNED/"isolated.py")
native=iso.load_native(PINNED/"native_source.py")
front=load("dispatch_front",DISPATCH/"replay.py")
assert blob(CORE.read_bytes())==front.CORE_HASH
core=load("frozen_core",CORE)

def sample(fork,col,right):
    bay=(col,0)
    standby=(col,1)
    w=iso.make(native,False)
    p,q=w.agents
    p.x,p.y,p.dir=col+1 if right else col-1,0,(
                  native.Direction.LEFT if right else native.Direction.RIGHT)
    q.x,q.y,q.dir=col,1,native.Direction.UP
    side=native.Agent(1,3,native.Direction.RIGHT,0)
    w.agents.append(side)
    w.n_agents=3
    w._recalc_grid()
    def cut():
        scope_open=all((m.x,m.y)!=bay for m in w.agents)
        q_ready=(q.x,q.y)==standby
        p_out=(p.x,p.y)!=bay
        return (scope_open,q_ready,p_out)
    initial=cut()
    assert initial==(True,True,True)
    stay=native.Action.NOOP.value
    forward=native.Action.FORWARD.value
    # No two moving arcs in the same weak component; this is within
    # the pinned source isolator's narrowly exercised graph fixture.
    native.step(w,[forward if fork=="incumbent" else stay,
                   forward if fork=="reserve" else stay,forward])
    after=cut()
    side_ok=(side.x,side.y)==(2,3)
    assert side_ok
    return initial,after,side_ok

def with_view(row,receipt,geometry=None):
    avail=((1,"replacement",("old-dispatch","P",0)),) if receipt else ()
    if geometry is not None:
        avail += ((1,"replacement",("consume-scope",*geometry)),)
    # Receipt and geometry are the only queries supplied to policy.
    return core.Row(avail,row.facts,row.events,row.options)

def select(admitted):
    return next((m for m in ("primary_inline","backup") if m in admitted),None)

def main():
    table=front.native_table()
    variants={}
    stat={"late_scope_success":0,"latched_inadmissible":0,"named_only_inadmissible":0,
          "new_refusals":0,"old_feasible_after_refusal":0}
    for col,right in product((1,2,3),(False,True)):
        worlds={name:sample(name,col,right) for name in ("neither","incumbent","reserve")}
        for prior,writer,receipt_live,fork in product((0,1),(0,1),(0,1),worlds):
            initial,now,side_ok=worlds[fork]
            g,q,p_out=now
            receipt=bool(prior and receipt_live)
            # Granular local paid evidence phases, no hidden order identifiers.
            # Without receipt, both paid and not-paid are possible (erasure).
            poss=(1,) if receipt else (0,1)
            answer=lambda pairs,shape: select(core.admitted(
                [with_view(front.world_row(core,table,old,writer,qv,gv),receipt,shape)
                 for old in poss for gv,qv in pairs],
                "replacement",1,front.DUE,front.OPTIONS)[
                    core.view(with_view(front.world_row(core,table,prior,writer,q,g),
                                        receipt,shape),"replacement",1)])
            exact=answer(((g,q),),(g,q))
            offline_direct=set.intersection(*(front.independent_formula(old,writer,q,g)
                                               for old in poss))
            assert exact==select(offline_direct)
            stale=answer((initial[:2],),initial[:2])
            # Better negative control: trust fresh reserve state, but
            # scope sample checks only the incumbent's own position.
            named=answer(((p_out,q),),(p_out,q))
            truly_admissible=front.independent_formula(prior,writer,q,g)
            stat["late_scope_success"]+=exact is not None
            stat["latched_inadmissible"]+=stale is not None and stale not in truly_admissible
            stat["named_only_inadmissible"]+=named is not None and named not in truly_admissible
            stat["new_refusals"]+=exact is None
            if exact is None:
                preserve=table[prior,writer,0,0,0]
                assert preserve["side"] and side_ok
                stat["old_feasible_after_refusal"]+=bool(preserve["past"] or preserve["pforce"])
            else:
                release,ip,backup=front.OPTIONS[exact]
                installed=table[prior,writer,release,ip,backup]
                assert exact in truly_admissible
                assert installed["side"] and side_ok
                assert installed["past"] or installed["pforce"]
                assert installed["pvel"]+installed["qvel"]==1
            if col==2 and right and (prior,writer,receipt_live)==(1,1,1):
                variants[fork]={"scope_open":g,"backup_staged":q,"incumbent_outside":p_out,
                                "fresh":exact,"early_snapshot":stale,"incumbent_only":named}
    assert variants["neither"]["fresh"]=="primary_inline"
    assert variants["incumbent"]["fresh"]=="backup"
    assert variants["reserve"]["fresh"] is None
    assert variants["reserve"]["incumbent_only"]=="primary_inline"
    print(json.dumps(dict(cases=6*8*3,stats=stat,witness=variants),sort_keys=True))

if __name__=="__main__":main()
