#!/usr/bin/env python3
"""Finite conditional event generator and comparison against serial native RMF."""
from dataclasses import dataclass, replace
from collections import defaultdict
from collections.abc import Callable
from itertools import permutations
from pathlib import Path
import json
from math import factorial

HERE = Path(__file__).resolve().parent

@dataclass(frozen=True)
class Event:
    name: str
    requires: frozenset[str]
    step: Callable

def generate(events, initial):
    """Produce the entire observation relation, without using native trace data."""
    def rec(used, state, trace):
        if len(used)==len(events):
            yield trace
            return
        for e in events:
            if e.name not in used and e.requires <= used:
                nxt, obs=e.step(state)
                yield from rec(used | {e.name}, nxt, trace+((e.name,obs,nxt),))
    return rec(frozenset(), initial, ())

@dataclass(frozen=True)
class Bay:
    incumbent: bool = True
    far_done: bool = False
    a_intent: bool = False
    ready: frozenset = frozenset()
    pending: tuple = ()
    span: str = ""

    def observable(self, forwarding=False):
        # Trace comparator, not an assumed view of any one receiver.
        return "".join(map(str, (int("A" in self.ready),int(self.span=="A"),
            int("B" in self.ready),int(self.span=="B"),int(self.far_done),
            int(not self.incumbent),int(self.a_intent),int(forwarding))))

    def queue(self, actor):
        if actor in self.ready:
            return self
        return replace(self, ready=self.ready | {actor}, pending=self.pending+(actor,))

    def resolve(self):
        if self.incumbent or self.span or not self.pending:
            return self
        return replace(self, span=self.pending[0], pending=self.pending[1:])

def effect(s, event, qualified):
    forward=False
    if event=="A":
        s=replace(s,a_intent=True).queue("A")
    elif event=="B":
        s=s.queue("B")
    elif event=="C":
        s=replace(s,incumbent=False)
    elif event=="W":
        s=replace(s,a_intent=False,ready=s.ready-{"A"},span="" if s.span=="A" else s.span,
                  pending=tuple(w for w in s.pending if w!="A"))
    elif event=="R":
        forward=not qualified or s.a_intent
        if forward:
            s=s.queue("A")
    elif event=="X":
        s=replace(s,far_done=True)
    else:
        raise ValueError(event)
    t=s.resolve()
    return t, t.observable(forward)

def source_read():
    result={}
    for line in (HERE/"NATIVE.txt").read_text().splitlines():
        arm,word,*hits=line.split()
        assert len(hits)==6 and all(len(h)==8 for h in hits)
        key=(int(arm),word)
        assert key not in result
        result[key]=hits
    return result

def main():
    native=source_read()
    derived={}
    graphs=[]
    per_arm=[]
    for q in (0,1):
        events=tuple(Event(name,frozenset({"A"} if name in "RW" else ()),
                           lambda s,n=name:effect(s,n,q)) for name in "ABCRWX")
        traces=list(generate(events,Bay()))
        prefix={}
        for t in traces:
            w="".join(e[0] for e in t)
            derived[q,w]=[e[1] for e in t]
            for i,(_,z,s) in enumerate(t,1):
                prefix[w[:i]]=(z,s)
        graphs.append(prefix)
        settled=defaultdict(set)
        for w,(z,_) in prefix.items():
            if w.endswith("C"):
                # Local controller sees only allocator bounds/receipt fact,
                # not evaluator intent or exact forwarding log.
                p=w[:-1]
                before=prefix[p][0][:6] if p else "000000"
                settled[before].add(z[:6])
        per_arm.append(dict(paths=len(traces),prefixes=len(prefix),
                            widest_clear_support=max(map(len,settled.values()))))
    if derived!=native:
        wrong=[(k,derived.get(k),native.get(k)) for k in derived.keys() | native.keys()
               if derived.get(k)!=native.get(k)]
        raise AssertionError(wrong[:12])
    for q in (0,1):
        p=graphs[q]
        assert p["AB"][0]==p["BA"][0]
        assert p["ABC"][0][1:4:2]=="10"
        assert p["BAC"][0][1:4:2]=="01"
        # First delivery A, withdrawn, held notification then goes to use.
        # Contender B and exit are the common remaining events.
    assert graphs[0]["AWRBC"][0][1:4:2]=="10"
    assert graphs[1]["AWRBC"][0][1:4:2]=="01"
    # Common-source incompatibility: in no complete replay are both
    # contenders issued the exclusive segment at one physical cut.
    # Their independent possibility sets would admit that invented tuple.
    assert all(z[1:4:2]!="11" for obs in native.values() for z in obs)
    assert all(any(z[1:4:2]==x for obs in native.values() for z in obs) for x in ("10","01"))
    # X commutes on the projected crossing transcript, but only through
    # unobserved placement of the independent effect. It is still owed.
    quotient={}
    for (q,w),obs in native.items():
        k=(q,w.replace("X",""))
        pruned=tuple(o[:4]+o[5:] for e,o in zip(w,obs) if e!="X")
        assert obs[w.index("X")][4]=="1"
        if k in quotient:
            assert quotient[k]==pruned
        else:
            quotient[k]=pruned
    assert len(quotient)==80 and len(native)==480
    # Count the exact number of reusable boundary summaries when a
    # subsequent customer can withdraw at most k named contenders.
    states={}
    query_checks=0
    for n in range(2,6):
        q=tuple(range(n))
        for k in range(n):
            masks=[mask for mask in range(1<<n) if mask.bit_count()<=k]
            table={}
            for p in permutations(q):
                answers=tuple(next(i for i in p if not mask&(1<<i)) for mask in masks)
                prefix=p[:k+1]
                assert table.setdefault(answers,prefix)==prefix
                query_checks+=len(masks)
            assert len(table)==factorial(n)//factorial(n-k-1)
            states[f"{n}/{k}"]=len(table)
    count=(HERE/"QUERY-COUNTS.txt").read_text().strip()
    assert count=="deletion queries "+str(sum(factorial(n)*(1<<n) for n in range(2,6)))
    print(json.dumps({"native_schedules":len(native),"projected_schedules":len(quotient),
                      "native_deletion_queries":int(count.split()[-1]),
                      "bounded_query_checks":query_checks,"minimum_summary_states":states,
                      "cases":per_arm},sort_keys=True))
if __name__=="__main__":
    main()
