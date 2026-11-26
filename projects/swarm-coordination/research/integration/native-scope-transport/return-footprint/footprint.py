"""Cached local return interface; facts must come from actual effects."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Footprint:
    cargo: str
    carrier: str | None
    settled: bool
    storage: tuple[int,int] | None

def available(x, cell):
    if not x.settled or x.carrier is not None or x.storage is None:
        return None
    return x.storage!=cell
