from dataclasses import dataclass

@dataclass(frozen=True)
class FootprintCut:
    old_sources_sealed: bool
    old_entering_pending: int
    old_duty_discharged: bool
    empty_now: bool

def may_admit(w):
    return (w.old_sources_sealed and w.old_entering_pending==0
            and w.old_duty_discharged and w.empty_now)
