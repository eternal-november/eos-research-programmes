"""Reference finite-configuration occurrence machine.

Trusted Python callbacks stand for parameterized data/primitive families. This is
not a parser or static type checker. The scheduler is explicit; prefix limits are
observations, never semantic failures. Exact arithmetic and raw zero-weight edges
are retained. The global event ledger, not a terminal-result product, measures a
concurrent execution. See README.md for the supported fragment and boundaries.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from copy import deepcopy
from typing import Any, Callable

@dataclass(frozen=True)
class Leaf:
    value: Any
    caps: tuple[str, ...] = ()

@dataclass(frozen=True)
class Node:
    label: str
    children: tuple[Any, ...] = ()
    structural: bool = False


def leaves(tree):
    if isinstance(tree, Leaf):
        return [tree]
    return [x for t in tree.children for x in leaves(t)]


def graft(tree, replacements):
    it = iter(replacements)
    def go(t):
        if isinstance(t, Leaf):
            return next(it)
        return Node(t.label, tuple(go(c) for c in t.children), t.structural)
    ans = go(tree)
    try:
        next(it)
        raise ValueError('too many graft replacements')
    except StopIteration:
        return ans

@dataclass(frozen=True)
class Ret:
    f: Callable[[Any], Any] = lambda x: x
@dataclass(frozen=True)
class Op:
    name: str
    arg: Callable[[Any], Any] = lambda x: x
@dataclass(frozen=True)
class Bind:
    left: Any
    k: Callable[[Any], Any]
@dataclass(frozen=True)
class Batch:
    # Entries (term, data input, exact token bundle). Split is checked at runtime.
    split: Callable[[Any, tuple[str, ...]], tuple]
@dataclass(frozen=True)
class Call:
    name: str
    arg: Callable[[Any], Any] = lambda x: x
@dataclass(frozen=True)
class ProcedureEntry:
    term: Any
    value: Any
@dataclass(frozen=True)
class Choice:
    terms: tuple[Any, ...]
@dataclass(frozen=True)
class Case:
    select: Callable[[Any], int]
    terms: tuple[Any, ...]
@dataclass(frozen=True)
class Yield:
    next: Any
@dataclass(frozen=True)
class Spawn:
    term: Any
    take: Callable[[Any, tuple[str, ...]], tuple[str, ...]]
    arg: Callable[[Any], Any] = lambda x: x
@dataclass(frozen=True)
class Send:
    channel: str
    take: Callable[[Any, tuple[str, ...]], tuple[str, ...]]
    payload: Callable[[Any], Any] = lambda x: x
@dataclass(frozen=True)
class Receive:
    channel: str
@dataclass(frozen=True)
class Await:
    handle: Callable[[Any], int] = lambda x: x
    reserve: Callable[[Any], Any] = lambda x: None
@dataclass(frozen=True)
class Fault:
    reason: str

@dataclass(frozen=True)
class Outcome:
    witness: str
    weight: Fraction
    cost: tuple[int, ...]
    event: str
    tree: Any
    world: Any
    consume: tuple[str, ...] = ()
    retype: dict[str, str] = field(default_factory=dict)
    stores: dict[str, Any] = field(default_factory=dict)
    mint: dict[str, str] = field(default_factory=dict)

@dataclass
class Result:
    tree: Any
    raw: Any
    events: tuple[int, ...] = ()
    status: str = 'returned'

@dataclass
class Job:
    term: Any
    value: Any
    rank: tuple[int, ...]
    mode: str = 'eval'
    waiting: Any = None
    result: Result | None = None
    parent: int | None = None
    claimed: bool = False

class Machine:
    def __init__(self, term, value=None, *, caps=(), kinds=None, stores=None,
                 world=None, primitives=None, procedures=None, cost_dimension=1,
                 allow_mint=False):
        if len(caps) != len(set(caps)):
            raise ValueError('duplicate initial authority')
        self.jobs = {0: Job(term, value, (0,))}
        self.ledger = {c: ('job', 0) for c in caps}
        self.kinds = dict(kinds or {c: 'token' for c in caps})
        self.stores = deepcopy(stores or {})
        self.world = deepcopy(world if world is not None else {})
        self.primitives = primitives or {}
        self.procedures = procedures or {}
        self.cost_dimension = cost_dimension
        self.allow_mint = allow_mint
        self.messages = {}
        self.queues = {}
        self.events = []
        self.trace = []
        self.next_job = 1
        self.next_message = 0
        self.assert_invariant()

    def owned(self, location):
        return tuple(sorted(c for c, loc in self.ledger.items() if loc == location))

    def validate_transfer(self, caps, src):
        if len(caps) != len(set(caps)) or any(self.ledger.get(c) != src for c in caps):
            raise ValueError('unauthorized or duplicate transfer')

    def transfer(self, caps, src, dst):
        self.validate_transfer(caps, src)
        for c in caps:
            self.ledger[c] = dst

    def new_job(self, term, value, caps, src, rank, parent=None):
        self.validate_transfer(caps, src)
        pid = self.next_job
        self.next_job += 1
        self.jobs[pid] = Job(term, value, rank, parent=parent)
        self.transfer(caps, src, ('job', pid))
        return pid

    def finish(self, pid, result):
        caps = tuple(c for x in leaves(result.tree) for c in x.caps)
        if len(caps) != len(set(caps)) or set(caps) != set(self.owned(('job', pid))):
            raise ValueError('result does not partition current job authority')
        self.transfer(caps, ('job', pid), ('result', pid))
        self.jobs[pid].result = result
        self.jobs[pid].mode = 'done'

    def claim(self, child, parent):
        j = self.jobs[child]
        if j.mode != 'done' or j.claimed:
            raise ValueError('result unavailable')
        j.claimed = True
        self.transfer(self.owned(('result', child)), ('result', child), ('job', parent))
        return j.result

    def enabled(self):
        out = []
        for pid, j in self.jobs.items():
            if j.mode == 'done':
                continue
            if j.mode == 'left':
                if self.jobs[j.waiting[0]].mode == 'done': out.append(pid)
            elif j.mode == 'join':
                if all(self.jobs[c].mode == 'done' for c in j.waiting['children']): out.append(pid)
            elif isinstance(j.term, Receive):
                if self.queues.get(j.term.channel): out.append(pid)
            elif isinstance(j.term, Await):
                h = j.term.handle(j.value)
                if h not in self.jobs or self.jobs[h].claimed or self.jobs[h].parent is not None or self.jobs[h].mode == 'done': out.append(pid)
            else:
                out.append(pid)
        return out

    def phase_next(self):
        ready = self.enabled()
        return min(ready, key=lambda p: self.jobs[p].rank) if ready else None

    def validate_outcome(self, pid, o):
        held = set(self.owned(('job', pid)))
        consumed = set(o.consume)
        new = set(o.mint)
        caps = [c for x in leaves(o.tree) for c in x.caps]
        if (not isinstance(o.weight, (Fraction, int)) or isinstance(o.weight, bool)
                or any(not isinstance(c, int) or isinstance(c, bool) for c in o.cost)):
            raise ValueError("weights must be rational and costs natural integers")
        if o.weight < 0 or len(o.cost) != self.cost_dimension or any(c < 0 for c in o.cost):
            raise ValueError('invalid coefficient')
        if len(o.consume) != len(consumed) or not consumed <= held:
            raise ValueError('invalid consumed authority')
        if new & set(self.ledger) or (new and not self.allow_mint):
            raise ValueError('unauthorized mint')
        if len(caps) != len(set(caps)) or set(caps) != (held-consumed)|new:
            raise ValueError('primitive post-tree must exactly partition retained authority')
        if not set(o.retype) <= held | new or not set(o.stores) <= held | new:
            raise ValueError('primitive changes another owner private state')

    def step(self, pid=None, *, alternative=0, outcome=0, choice=0, message=0):
        if pid is None: pid = self.phase_next()
        if pid is None: return False
        if pid not in self.enabled(): raise ValueError('job is not enabled')
        j = self.jobs[pid]
        self.trace.append(('schedule', pid, j.mode))
        if j.mode == 'left':
            child, k = j.waiting
            left = self.claim(child, pid)
            if left.status != 'returned':
                self.finish(pid, left)
            else:
                children = []
                for i, leaf in enumerate(leaves(left.tree)):
                    children.append(self.new_job(k(leaf.value), leaf.value, leaf.caps,
                        ('job', pid), j.rank+(1,i), pid))
                j.mode = 'join'
                j.waiting = dict(kind='bind', left=left, children=children)
        elif j.mode == 'join':
            w = j.waiting
            results = [self.claim(c, pid) for c in w['children']]
            if w['kind'] == 'bind':
                left = w['left']
                tree = graft(left.tree, [r.tree for r in results])
                raw = ('bind', left.raw, tuple(r.raw for r in results))
                ids = left.events + tuple(e for r in results for e in r.events)
            else:
                tree = Node('Fork', tuple(r.tree for r in results), True)
                raw = ('batch', tuple(r.raw for r in results))
                ids = tuple(e for r in results for e in r.events)
            status = 'fault' if any(r.status != 'returned' for r in results) else 'returned'
            self.finish(pid, Result(tree, raw, ids, status))
        else:
            t = j.term
            held = self.owned(('job', pid))
            if isinstance(t, Ret):
                self.finish(pid, Result(Leaf(t.f(j.value), held), ('ret',)))
            elif isinstance(t, Fault):
                self.finish(pid, Result(Leaf({'fault':t.reason}, held), ('fault',t.reason), status='fault'))
            elif isinstance(t, Bind):
                child = self.new_job(t.left, j.value, held, ('job',pid), j.rank+(0,), pid)
                j.mode, j.waiting = 'left', (child,t.k)
            elif isinstance(t, Batch):
                entries = tuple(t.split(j.value,held))
                assigned = [c for _,_,cs in entries for c in cs]
                if len(assigned)!=len(set(assigned)) or set(assigned)!=set(held):
                    raise ValueError('batch requires an exact separated partition, including reserve')
                children = [self.new_job(term,value,tuple(cs),('job',pid),j.rank+(i,),pid)
                            for i,(term,value,cs) in enumerate(entries)]
                j.mode, j.waiting = 'join', dict(kind='batch', children=children)
            elif isinstance(t, Op):
                alts = tuple(tuple(a) for a in self.primitives[t.name](
                    t.arg(j.value), held, deepcopy(self.world), deepcopy({c:self.stores[c] for c in held if c in self.stores})))
                if not alts: raise ValueError('empty primitive alternatives')
                for alt in alts:
                    if not alt or sum((o.weight for o in alt), Fraction(0)) != 1:
                        raise ValueError('primitive law is not normalized')
                    for o in alt: self.validate_outcome(pid,o)
                o = alts[alternative][outcome]
                for c in o.consume: self.ledger[c] = ('retired', c)
                for c,kind in o.mint.items(): self.ledger[c]=('job',pid);self.kinds[c]=kind
                self.kinds.update(o.retype); self.stores.update(deepcopy(o.stores))
                self.world = deepcopy(o.world)
                eid=len(self.events)
                self.events.append(dict(pid=pid,name=t.name,witness=o.witness,weight=o.weight,cost=o.cost,event=o.event))
                self.finish(pid,Result(o.tree,('op',t.name,alternative,outcome,o.witness),(eid,)))
            elif isinstance(t, Call):
                arg = t.arg(j.value)
                entry = self.procedures[t.name](arg)
                if isinstance(entry, ProcedureEntry):
                    j.term, j.value = entry.term, entry.value
                else:
                    j.term, j.value = entry, arg
                self.trace.append(('unfold',pid,t.name))
            elif isinstance(t, Choice):
                if not t.terms: raise ValueError('empty choice')
                j.term=t.terms[choice];self.trace.append(('choice',pid,choice))
            elif isinstance(t, Case):
                branch=t.select(j.value);j.term=t.terms[branch]
                self.trace.append(('case',pid,branch))
            elif isinstance(t, Yield): j.term=t.next;self.trace.append(('yield',pid))
            elif isinstance(t, Spawn):
                cs=tuple(t.take(j.value,held))
                child=self.new_job(t.term,t.arg(j.value),cs,('job',pid),(self.next_job,),None)
                self.finish(pid,Result(Leaf(child,self.owned(('job',pid))),('spawn',child)))
            elif isinstance(t, Send):
                cs=tuple(t.take(j.value,held))
                self.validate_transfer(cs, ("job",pid))
                payload=deepcopy(t.payload(j.value))
                mid=self.next_message;self.next_message+=1
                self.transfer(cs,('job',pid),('msg',mid))
                self.messages[mid]=(t.channel,payload)
                self.queues.setdefault(t.channel,[]).append(mid)
                self.finish(pid,Result(Leaf(mid,self.owned(('job',pid))),('send',mid)))
            elif isinstance(t, Receive):
                mid=self.queues[t.channel].pop(message)
                _,payload=self.messages.pop(mid)
                self.transfer(self.owned(('msg',mid)),('msg',mid),('job',pid))
                self.finish(pid,Result(Leaf(payload,self.owned(('job',pid))),('receive',mid)))
            elif isinstance(t, Await):
                h=t.handle(j.value)
                if h not in self.jobs or self.jobs[h].claimed or self.jobs[h].parent is not None:
                    self.finish(pid,Result(Leaf({'refused':'unavailable result'},held),('await-refused',h)))
                else:
                    r=self.claim(h,pid)
                    # Explicit reserve child prevents duplicating caller caps over child leaves.
                    tree=Node('Fork',(r.tree,Leaf(t.reserve(j.value),held)),True)
                    self.finish(pid,Result(tree,('await',h,r.raw),r.events,r.status))
            else: raise TypeError(type(t))
        self.assert_invariant()
        return True

    def environment_step(self, label, update):
        """Declared world-only interference; cannot alter frontier token ownership.

        update is a trusted pure callback on a world snapshot. A larger signature
        with ledger-changing deviations needs a separate checked transaction.
        """
        self.world = deepcopy(update(deepcopy(self.world)))
        self.trace.append(('environment', label))
        self.assert_invariant()

    def prefix(self, limit, scheduler=None, stop_at_root=False):
        """Inspect at most limit steps. Never creates a fuel-exhausted result."""
        for _ in range(limit):
            if stop_at_root and self.jobs[0].mode=='done': break
            pid = scheduler(self) if scheduler else self.phase_next()
            if pid is None: break
            self.step(pid)
        return self

    @property
    def weight(self):
        p=Fraction(1)
        for e in self.events:p*=e['weight']
        return p
    @property
    def cost(self):
        return tuple(sum(e['cost'][i] for e in self.events) for i in range(self.cost_dimension))
    @property
    def word(self):return tuple(e['event'] for e in self.events)

    def assert_invariant(self):
        for c,loc in self.ledger.items():
            kind,ident=loc
            if kind=='job': assert ident in self.jobs and self.jobs[ident].mode!='done'
            elif kind=='result': assert ident in self.jobs and self.jobs[ident].mode=='done' and not self.jobs[ident].claimed
            elif kind=='msg': assert ident in self.messages
            elif kind!='retired': raise AssertionError(loc)
            assert c in self.kinds
        for pid,j in self.jobs.items():
            if j.mode=='done' and not j.claimed:
                cs=[c for leaf in leaves(j.result.tree) for c in leaf.caps]
                assert len(cs)==len(set(cs)) and set(cs)==set(self.owned(('result',pid)))
            if j.mode in ('left','join'): assert not self.owned(('job',pid))
        for channel,ids in self.queues.items():
            assert len(ids)==len(set(ids))
            assert all(self.messages[mid][0]==channel for mid in ids)
