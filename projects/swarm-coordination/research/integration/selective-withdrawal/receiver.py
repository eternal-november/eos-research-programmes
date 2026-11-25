"""Frozen reference receiver; discrete time; no runtime or hardware integration."""
from dataclasses import dataclass
from enum import Enum

class Kind(Enum):
    QUIESCENT = 'old physical effect absent'
    FENCED = 'old commands cannot take effect'
    GRANTED = 'new action exclusively authorized with capacity reserved'

@dataclass(frozen=True)
class Key:
    kind: Kind
    scope: str       # physical interference class or shared capacity unit
    old: str         # old generation, not just producer name
    new: str         # new operation nonce, including its bound footprint

@dataclass(frozen=True)
class Fact:
    key: Key
    received: int    # at this receiver, on the normalized tick clock
    lower: int       # inclusive first guaranteed tick
    upper: int       # exclusive endpoint of the actual guarantee

@dataclass(frozen=True)
class Job:
    required: frozenset[Key]
    earliest: int    # not before this tick
    latest_end: int  # end of the protected effect, not issue time
    duration: int    # worst-case protected duration, strictly positive

def choose(job: Job, cut: int, facts: list[Fact]) -> int | None:
    """Earliest certified future start from evidence at cut, or no admission.
    A future start is a schedule, not permission to send the command early.
    Adapter supplies at most one normalized interval per key at any cut.
    """
    if cut < 0 or not 0 <= job.earliest <= job.latest_end or job.duration <= 0 or not job.required:
        raise ValueError('invalid job')
    found = {}
    for fact in facts:
        if fact.received > cut or fact.key not in job.required:
            continue
        if not 0 <= fact.received or not 0 <= fact.lower < fact.upper or fact.key in found:
            raise ValueError('invalid or ambiguous interval')
        found[fact.key] = fact
    if found.keys() != job.required:
        return None
    start = max(cut, job.earliest, *(fact.lower for fact in found.values()))
    end = min(job.latest_end, *(fact.upper for fact in found.values()))
    return start if start + job.duration <= end else None
