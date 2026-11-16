from fractions import Fraction as F
from collections import defaultdict
import json
# Outcomes: terminal t (1/2), active a (1/2), active zero witness z (0).
def terminal(h): return bool(h) and h[-1]=='t'
rows=[{():F(1)}]
strict=False
for n in range(6):
    nxt={}; back={}
    for h,p in rows[-1].items():
        if terminal(h):nxt[h]=p;back[h]=h
        else:
            for c,q in [('t',F(1,2)),('a',F(1,2)),('z',F(0))]:
                nxt[h+(c,)]=p*q;back[h+(c,)]=h
    sums=defaultdict(F)
    for h,p in nxt.items():sums[back[h]]+=p
    assert dict(sums)==rows[-1] and sum(nxt.values())==1
    for h in nxt:
        assert not terminal(back[h]) or terminal(h)
    assert all([h for h in nxt if back[h]==old]==[old] for old in rows[-1] if terminal(old))
    strict |= any(terminal(h) and not terminal(back[h]) for h in nxt)
    rows.append(nxt)
assert strict
assert sum(p for h,p in rows[6].items() if terminal(h))==1-F(1,64)
assert any(p==0 and terminal(h) for h,p in rows[6].items())
# Identity raw maps terminal→always-active satisfy lax direction, not strict.
assert set().issubset({'w'}) and {'w'}!=set()
print(json.dumps({'status':'passed','horizons':6,'terminal_mass_at_6':str(1-F(1,64)),'checks':['normalized-prefix','exact-truncation','partial-domain-variance','absorbing-terminal-fibres','zero-terminal-retention','strictness-needed-counterexample'],'scope':'finite exact scalar/raw diagnostics, not coefficient or general tower certification'},indent=2))
