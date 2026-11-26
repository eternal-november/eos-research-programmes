"""Ordered finite scope checker for an explicitly licensed actual queue."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Item:
    name: str
    resources: frozenset
    inputs: frozenset

def choose(queue, missing):
    """Greatest same-cut set that does not overtake held earlier resource work."""
    held = set()
    serve, retain = [], []
    for job in queue:
        assert job.resources
        if (job.inputs & missing) or (job.resources & held):
            retain.append(job.name)
            held.update(job.resources)
        else:
            serve.append(job.name)
    return tuple(serve),tuple(retain)
