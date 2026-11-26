"""Finite prefix interpreter and one-cut robust admission. No plant branches."""
from dataclasses import dataclass
from collections import Counter, defaultdict

@dataclass(frozen=True)
class Use:
    key: tuple
    count: int
    limit: int
    window: int
    deposit: bool = True

@dataclass(frozen=True)
class Event:
    at: int
    order: int
    need: frozenset = frozenset()
    absent: frozenset = frozenset()
    add: frozenset = frozenset()
    drop: frozenset = frozenset()
    uses: tuple = ()
    paid: tuple = ()

@dataclass(frozen=True)
class Row:
    receipts: tuple     # (available, recipient, content); not known-in-hindsight
    facts: frozenset
    events: tuple
    options: dict        # same names, but the physical consequence may differ

def view(row, actor, cut):
    return tuple((t, x) for t, who, x in row.receipts if t <= cut and who == actor)

def check(row, name, cut, dues, work=None):
    if work is not None:
        work['queries']+=1
    added = row.options.get(name)
    if added is None or any(e.at < cut for e in added):
        return False
    events = sorted(row.events+added,key=lambda e:(e.at,e.order))
    assert len({(e.at,e.order) for e in events}) == len(events)
    facts = set(row.facts)
    ledger = defaultdict(list)
    paid = Counter()
    late = set()
    for e in events:
        if work is not None:
            work['event_visits']+=1
        if not e.need <= facts or e.absent & facts:
            return False
        assert len({u.key for u in e.uses}) == len(e.uses)
        for u in e.uses:
            if work is not None:
                work['meter_checks']+=1
                work['prior_debit_row_reads']+=len(ledger[u.key])
            active = sum(n for t,n in ledger[u.key] if t >= e.at-u.window)
            if active+u.count > u.limit:
                return False
        for u in e.uses:
            if u.deposit:
                ledger[u.key].append((e.at,u.count))
        for d in e.paid:
            paid[d] += 1
            if d not in dues or e.at > dues[d]:
                late.add(d)
        facts.difference_update(e.drop)
        facts.update(e.add)
    return not late and paid == Counter({k:1 for k in dues})

def admitted(rows, actor, cut, dues, names):
    cells=defaultdict(list)
    for row in rows:
        cells[view(row,actor,cut)].append(row)
    return {obs:tuple(n for n in names if all(check(r,n,cut,dues) for r in cell))
            for obs,cell in cells.items()}

@dataclass(frozen=True)
class Fragment:
    binding: tuple      # latent episode/interface compatibility, NOT a receipt
    receipts: tuple
    facts: frozenset
    events: tuple

def join(left, right, options):
    """Equijoin on a declared joint-history label; never exposes the label."""
    left,right=tuple(left),tuple(right)
    if {r.binding for r in left}!={r.binding for r in right} or not left:
        # An unmatched binding is not a certified unreachable history.
        # Reject at this boundary rather than accept by dropping the row.
        raise ValueError("unaccounted joint-history binding")
    idx=defaultdict(list)
    for r in right:
        idx[r.binding].append(r)
    return [Row(tuple(sorted(l.receipts+r.receipts,key=lambda x:x[0])),
                l.facts|r.facts,l.events+r.events,options)
            for l in left for r in idx[l.binding]]
