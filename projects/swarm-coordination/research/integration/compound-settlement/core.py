"""Common local decision at a finite settlement cut."""
from dataclasses import dataclass
from enum import Enum, auto

class Old(Enum):
    SETTLED = auto()
    LIVE = auto()
    UNRESOLVED = auto()

@dataclass(frozen=True)
class Cut:
    old: Old
    # Local facility/airtime permissions for ordinary single effects at cutoff.
    usable: tuple[bool,bool]

def decide(cut):
    """Return (old fallback, rescue) on two sites; '-' means no issue.

    The old fallback is staged at R only. The rescue copies are staged at both.
    Only one effect of either duty is allowed on a site in this wave.
    Independent work is outside the two permissions and always continues.
    """
    left,right=cut.usable
    if cut.old is Old.UNRESOLVED:
        return '-','-'
    if cut.old is Old.SETTLED:
        return '-', 'L' if left else 'R' if right else '-'
    if not right:
        return '-','L' if left else '-'
    return 'R','L' if left else '-'
