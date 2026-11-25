"""Exact local action search against a compiled admission boundary.

Absolute ticks; support required on [s,s+h), shared resource spent on [s,s+h).
A read may be correct in the reservation epoch and still fail the physical law.
"""
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class Config:
    revoke: int      # earliest exogenous *or controlled* removal in these traces
    lead: int        # guaranteed advance warning, seen before a same-tick start
    command_end: int # fence prevents controlled removal strictly before this tick
    physics_end: int # independent uncommanded failure is possible from this tick
    handoff: int
    old_end: int
    report: int      # shared station must be clear by this tick for the report
    cutoff: int      # when receiver can last reconsider which plan to run

    @property
    def floor(self):
        return min(max(self.command_end, self.revoke), self.physics_end)

def world_sequences(c):
    # A disturbance flag is emitted exactly lead ticks before physical loss.
    # Negative emission times mark already advertised losses at experiment start.
    return [None, *range(c.floor, c.cutoff + c.handoff + c.lead + 1)]

def ref(c):
    """Enumerate start/continue-on-silence schedules; explicit traces."""
    for start in range(c.cutoff + 1):
        good = True
        for fail in world_sequences(c):
            # On warning before dispatch, retaining the old holder is only a
            # productive alternative when it remains available through report.
            notified = fail is not None and fail - c.lead <= start
            if notified:
                good &= c.old_end >= c.report
                continue
            finish = start + c.handoff
            good &= finish <= min(c.old_end, c.report)
            if fail is not None:
                good &= all(t < fail for t in range(start, finish))
            if not good:
                break
        if good:
            return start
    # Extending the old duty through report also serves the report.
    return c.cutoff+1 if c.old_end >= c.report else None

def compiled(c):
    for start in range(c.cutoff + 1):
        finish = start + c.handoff
        if finish > min(c.old_end, c.report):
            continue
        if c.old_end < c.report and c.floor <= start + c.lead:
            continue
        if finish > max(c.floor, start + c.lead + 1):
            continue
        return start
    return c.cutoff+1 if c.old_end >= c.report else None

def check():
    n=0
    for c in map(lambda x:Config(*x), product(range(4),range(4),range(6),range(1,8),range(1,5),range(1,7),range(1,7),range(4))):
        a,b = ref(c),compiled(c)
        assert a==b,(c,a,b)
        n+=1
    print(f"{n} exact earliest-admission comparisons")
    for name,c in [
      ("Snapshot only",Config(1,0,0,7,2,2,4,1)),
      ("Effector fence protects controlled mode",Config(1,0,2,7,2,2,4,1)),
      ("Same epoch cannot fence physical fault",Config(1,0,2,1,2,2,4,1)),
      ("Warning can help only with surviving service option",Config(1,1,0,7,2,4,4,1)),
    ]:
        print(name, compiled(c))

if __name__ == "__main__":
    check()

def family_ref(laws, start, duration, old_end, report):
    finish = start+duration
    if finish > min(old_end, report):
        return False
    for floor, lead in laws:
        for failure in range(floor, max(floor,finish,start+lead)+2):
            if failure-lead <= start:
                if old_end < report:
                    return False
            elif failure < finish:
                return False
    return True

def family_summary(laws, start):
    earliest_silent = min(max(F,start+L+1) for F,L in laws)
    warning_possible = any(F <= start+L for F,L in laws)
    return earliest_silent,warning_possible

def family_compiled(laws, start, duration, old_end, report):
    cut, warn = family_summary(laws,start)
    finish = start+duration
    return finish <= min(old_end, report, cut) and (not warn or old_end >= report)

def family_check():
    laws=list(product(range(1,7),range(4)))
    n=loss=0
    for a,b in product(laws,repeat=2):
        for s,h,old,d in product(range(3),range(1,5),range(2,7),range(2,7)):
            v=family_ref([a,b],s,h,old,d)
            assert v==family_compiled([a,b],s,h,old,d),(a,b,s,h,old,d)
            flat=family_compiled([(min(a[0],b[0]),min(a[1],b[1]))],s,h,old,d)
            # Shortening warning lead can shrink its early-warning branch.
            # If fallback itself is productive, the flattened check is
            # conservative; otherwise neither representation subsumes the other.
            if old>=d:
                assert not flat or v
                loss+=v and not flat
            n+=1
    print(f"{n} comparisons for two correlated source laws")
    print(f"{loss} strict false rejections of independent worst-case bounds with valid fallback")
    a,b=(1,3),(5,0)
    assert family_summary([a,b],0)==(4,True)
    assert family_compiled([a,b],0,4,5,5)
    assert not family_compiled([(1,0)],0,4,5,5)
    print("Correlated arm witness: exact earliest silent loss 4; flattened value 1")
    # Flattening can also mask the existence of an early warning and
    # approve an unsafe fallback. Here neither silent branch loses by finish,
    # but the first law can inhibit handoff at tick 0 and the holder expires.
    a,b=(1,1),(4,0)
    assert not family_compiled([a,b],0,1,1,2)
    assert family_compiled([(1,0)],0,1,1,2)
    print("No fallback witness: flattening drops a productive-service obligation")

if __name__ == "__main__":
    family_check()

def unrestricted_check():
    """Choose dispatch or productive fallback independently on each read."""
    laws=list(product(range(1,6),range(4)))
    n=0
    for a,b in product(laws,repeat=2):
        for s,h,old,d in product(range(3),range(1,4),range(1,6),range(1,6)):
            end=s+h
            times=[(False,None)] + [(t<=s+L,t) for F,L in [a,b]
                   for t in range(F,max(F,end,s+L)+1)]
            result=any(all((old>=d) if not table[read] else
                    (end<=min(old,d) and (t is None or end<=t))
                    for read,t in times) for table in product([False,True],repeat=2))
            if old>=d:
                exact=True
            else:
                exact=end<=min(old,d,a[0],b[0])
            assert result==exact,(a,b,s,h,old,d)
            n+=1
    print(f"{n} exact two-branch policy comparisons; no valid fallback requires surviving every arm")

if __name__ == "__main__":
    unrestricted_check()
