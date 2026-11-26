from dataclasses import dataclass

@dataclass(frozen=True)
class Cut:
    old_sources_sealed: bool
    old_before_dispatch: int
    old_after_dispatch: int
    old_duty_paid: bool

def can_open(cut):
    return (cut.old_sources_sealed and cut.old_before_dispatch == 0
            and cut.old_after_dispatch == 0 and cut.old_duty_paid)
