#!/usr/bin/env python3
"""Finite checks of operational local equations, persistent execution and source sharing.
These validate finite instances, not the general proof or physical model assumptions.
"""
import itertools
import json
from pathlib import Path

STATES=list(itertools.product(range(2), repeat=2))
IDX={x:i for i,x in enumerate(STATES)}
counts={"root_tables":0,"exact_component_local_equations":0,"persistent_conjugacy_steps":0,
        "task_summary_candidates":0,"autonomous_parity_models":0,"parity_persistent_steps":0,
        "delivered_interface_pairs":0,"legal_encoders":0}
for outputs in itertools.product(STATES,repeat=4):
    counts["root_tables"]+=1
    def F(x): return outputs[IDX[x]]
    # The unknown partition candidate consists of the two actual owned coordinates.
    # In each direction the message is the other OLD coordinate. Its provider is
    # checked, not silently treated as an external sensor.
    G0={(a,b):F((a,b))[0] for a,b in STATES}
    G1={(b,a):F((a,b))[1] for a,b in STATES}
    for x in STATES:
        y=x
        assert (G0[(y[0],y[1])],G1[(y[1],y[0])])==F(x)
        counts["exact_component_local_equations"]+=2
        for _ in range(5):
            x=F(x)
            y=(G0[(y[0],y[1])],G1[(y[1],y[0])])
            assert x==y
            counts["persistent_conjugacy_steps"]+=1
    # A noninjective summary is ONLY a task abstraction, not state reconstruction.
    valid=[]
    for gt in itertools.product(range(2),repeat=2):
        counts["task_summary_candidates"]+=1
        if all((F(x)[0]^F(x)[1])==gt[x[0]^x[1]] for x in STATES):
            valid.append(gt)
    expected=all((F(x)[0]^F(x)[1])==(F(y)[0]^F(y)[1])
                 for x in STATES for y in STATES if (x[0]^x[1])==(y[0]^y[1]))
    assert bool(valid)==expected
    if valid:
        assert len(valid)==1
        counts["autonomous_parity_models"]+=1
        gt=valid[0]
        for x in STATES:
            y=x[0]^x[1]
            for _ in range(5):
                x=F(x); y=gt[y]
                assert (x[0]^x[1])==y
                counts["parity_persistent_steps"]+=1
assert counts["root_tables"]==256
assert counts["autonomous_parity_models"]==64

# Every possible encoder on two bits is tested against every single-bit provider
# table. Existence of a delivered interface is exactly dependence on that provider.
for encoder in itertools.product(range(2),repeat=4):
    wires=[]
    for wt in itertools.product(range(2),repeat=2):
        counts["delivered_interface_pairs"]+=1
        if all(encoder[IDX[x]]==wt[x[0]] for x in STATES): wires.append(wt)
    dependence=all(encoder[IDX[x]]==encoder[IDX[y]] for x in STATES for y in STATES if x[0]==y[0])
    assert bool(wires)==dependence
    if wires:
        assert len(wires)==1
        counts["legal_encoders"]+=1
assert counts["legal_encoders"]==4
# Counterexample: update equation succeeds with inaccessible e=x1, but no wire
# reading only the selected component state x0 can provide that message.
encoder=tuple(x[1] for x in STATES)
assert all((x[0]^x[1])==(x[0]^encoder[IDX[x]]) for x in STATES)
assert not any(all(encoder[IDX[x]]==wt[x[0]] for x in STATES)
               for wt in itertools.product(range(2),repeat=2))

# A common stochastic source must remain common. Starting at 00, common z creates
# 00 or 11; independent copies also create 01 and 10 and break a parity property.
shared={(z,z) for z in range(2)}
independent=set(STATES)
assert shared=={(0,0),(1,1)} and len(independent-shared)==2
assert all(a^b==0 for a,b in shared)
assert sum(a^b for a,b in independent)==2
# Pointwise common-source equations guarantee preservation for arbitrary finite
# source paths, including temporally dependent or adversarial paths.
source_steps=0
for x0 in STATES:
    for seq in itertools.product(range(2),repeat=6):
        x=x0; y=x0
        for z in seq:
            x=(x[0]^z,x[1]^z)
            y=(y[0]^z,y[1]^z)
            assert x==y and (x[0]^x[1])==(x0[0]^x0[1])
            source_steps+=1
counts["common_source_path_steps"]=source_steps

# Non-Cartesian support qualification: x0=x1 permits apparent autonomy of x0'=x1;
# extending the claim to every Cartesian state is false.
assert all(x[1]==x[0] for x in STATES if x[0]==x[1])
assert any(x[1]!=x[0] for x in STATES)
# Scope selection is an unknown finite choice. Exhaustively compile one-output
# Boolean root maps using candidate scopes (), (0), (1), (0,1); all compatible
# maps must be found, and scope entries refer to the same current coordinates.
scope_checks=0; scope_solutions=0
for root in itertools.product(range(2),repeat=4):
    for scope in [(),(0,),(1,),(0,1)]:
        inputs=list(itertools.product(range(2),repeat=len(scope)))
        ix={a:i for i,a in enumerate(inputs)}
        found=[]
        for table in itertools.product(range(2),repeat=len(inputs)):
            scope_checks+=1
            if all(table[ix[tuple(x[k] for k in scope)]]==root[IDX[x]] for x in STATES):
                found.append(table)
        depends=all(root[IDX[x]]==root[IDX[y]] for x in STATES for y in STATES
                    if tuple(x[k] for k in scope)==tuple(y[k] for k in scope))
        assert bool(found)==depends
        if found:
            assert len(found)==1
            scope_solutions+=1
counts["scope_table_candidates"]=scope_checks
counts["scope_realizations"]=scope_solutions
# A repeated unknown table is one variable. Separate chart fits conflict when
# both pin the same entry to different values; copying the table would invent fit.
shared_tables=[t for t in itertools.product(range(2),repeat=2) if t[0]==0 and t[0]==1]
separate_tables=[(s,t) for s in itertools.product(range(2),repeat=2)
                 for t in itertools.product(range(2),repeat=2) if s[0]==0 and t[0]==1]
assert not shared_tables and len(separate_tables)==4
# The full message e=x1 realizes x0'=x0 xor x1. Constant postprocessing erases
# the necessary distinction; no unary new local update can repair it.
assert not any(all(gt[x[0]]==(x[0]^x[1]) for x in STATES)
               for gt in itertools.product(range(2),repeat=2))
result={"status":"PASS","counts":counts,"controls":[
    "inaccessible encoder rejected by delivered-interface equation",
    "task quotient distinguished from exact owned-state decomposition",
    "shared source not replaced by independent draws",
    "reachable-support completeness not promoted to Cartesian completeness",
    "scope search exact against full-domain dependence",
    "shared mechanism entry cannot be independently refitted",
    "noninvertible message coarsening can destroy realization"]}
out=Path(__file__).with_suffix('.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
