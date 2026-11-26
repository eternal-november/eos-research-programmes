"""Finite two-cut adapter over the unchanged single-cut evaluator."""
from core import admitted

def planes(candidates, actor, cut, dues, names):
    """Return accepted prefix -> view -> permitted terminal actions.

    Each prefix's rows must be the result of applying that prefix to all
    possible starting worlds with adequate provenance. A caller must not
    create the support by pruning failures. A missing/empty support is
    rejected, not treated as vacuously successful.
    """
    names=tuple(names)
    out={}
    for prefix, rows in candidates.items():
        rows=tuple(rows)
        if not rows:
            continue
        t=admitted(rows,actor,cut,dues,names)
        if all(t.values()):
            out[prefix]=t
    return out
