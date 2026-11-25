"""Finite civil report-return fixture. No live hardware or field deployment."""
from dataclasses import dataclass
from receiver import Fact, Job, Key, Kind, choose

KEYS={k:Key(k,"copy station","relay leg 0","mule leg 1") for k in Kind}
REQ=frozenset(KEYS.values())

@dataclass(frozen=True,order=True)
class Fault:
    notice: int     # when reserve sees relay cannot finish the old obligation
    gate: int       # effective no-old-entry evidence reaches reserve
    quiet: int      # sustained whole-station clearance evidence reaches reserve
    grant: int      # exclusive station grant reaches reserve
    duration: int   # protected copy, onward relay delivery and egress bound

@dataclass(frozen=True,order=True)
class Primary:
    receipt: int    # bound-for-duty base receipt, locally available

def envelope(cases, work, deadline):
    """Cumulative staging while no resolving message has arrived."""
    if not cases:
        raise ValueError("empty declared fault family")
    if work < 0 or any(not 0<=f.notice<=deadline or f.duration<=0 for f in cases):
        raise ValueError("invalid declared family")
    if any(max(f.notice,f.gate,f.quiet,f.grant)+f.duration>deadline
           for f in cases):
        return None
    requirements=[(f.notice, max(0,f.notice+work+f.duration-deadline)) for f in cases]
    if any(r>t or r>work for t,r in requirements):
        return None
    return tuple(max([0]+[r-max(0,t-u) for t,r in requirements])
                 for u in range(deadline+1))

def sender(f, cut, ready, deadline):
    if isinstance(f,Primary):
        return (f.receipt if f.receipt<=deadline else None),True
    # Commitments at old plant stay live until separate evidence. Native source
    # status is not accepted as the persistent fact; these are plant guarantees.
    facts=[Fact(KEYS[k],t,t,deadline+1)
           for k,t in ((Kind.QUIESCENT,f.quiet),(Kind.FENCED,f.gate),(Kind.GRANTED,f.grant))
           if t<deadline+1]
    if ready>deadline: return None,False
    job=Job(REQ,ready,deadline,f.duration)
    for t in range(cut,deadline+1):
        if (s:=choose(job,t,facts)) is not None:
            return s+f.duration,True
    return None,False

def trace(schedule, case, work, deadline):
    notice=case.receipt if isinstance(case,Primary) else case.notice
    # Actions chosen on the common all-silence prefix. Time slots after
    # resolving message cannot be charged to speculative preparation.
    spent=schedule[notice]
    ready=notice+work-spent
    received, admitted=sender(case,notice,ready,deadline)
    mandatory_independent_ticks=tuple(t for t in (1,3,5) if t<=deadline)
    # Scanning crew keeps original bytes through base receipt. A route change
    # alone never retires the named report duty; no phantom completion credit.
    report_unsettled_through=received if received is not None else deadline+1
    return received,spent,mandatory_independent_ticks,report_unsettled_through,admitted
