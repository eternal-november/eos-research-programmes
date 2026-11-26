"""Frozen proof-consumption profiles over a fixed continued mission."""
from dataclasses import dataclass

# Controller is frozen and never receives environment/plant identity.
# Qualified "old not yet paid" authorizes retry from R only at the audited cut.
FROZEN = (("LIVE",("R","L")),("SETTLED",("-","R")))
REQUIRED = (True,True,True)  # old delivery, rescue delivery, unaffected work

@dataclass(frozen=True)
class Row:
    law: str         # plant family/context and configured timing
    trace: tuple     # immutable identity of a native execution here
    status: str      # modeled available actual-settlement observation
    action: tuple    # after the observation cut
    paid: tuple      # measured effects

def selected(rows):
    table=dict(FROZEN)
    return tuple(r for r in rows if r.action==table[r.status])

def consumers(rows,select=selected):
    retained=select(rows)
    assert frozenset(r.status for r in retained)==frozenset(s for s,_ in FROZEN)
    return frozenset((r.status,r.action,r.paid) for r in retained)

def audit(rows,requirements=REQUIRED):
    scope=consumers(rows)
    return all(all(not want or got for want,got in zip(requirements,what,strict=True))
               for _,_,what in scope)

def join_effect(rows,wants):
    return tuple(r.trace for r in rows if all(r.paid[i] for i in wants))
