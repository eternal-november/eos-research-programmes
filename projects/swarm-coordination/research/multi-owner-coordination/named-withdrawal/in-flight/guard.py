"""An early named withdrawal depends on the actual live predecessor scope."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Right:
    held: bool
    object: str
    source_cell: tuple[int,int]

@dataclass(frozen=True)
class LiveScope:
    covers_pending: bool
    valid_through_cut: bool
    may_touch: frozenset

def admission(right,observed_object,observed_cell,predecessor):
    return (
        right.held and observed_object==right.object
        and observed_cell==right.source_cell and predecessor is not None
        and predecessor.covers_pending and predecessor.valid_through_cut
        and right.object not in predecessor.may_touch
    )
