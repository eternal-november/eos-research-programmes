"""Adjacent certificate transport for site membership, not a wire protocol."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Permutation:
    before_generation: int
    after_generation: int
    reverse: bool

def carry(start,known,target,records):
    if not known or not (0<=start<=target):
        return None
    version,placement=start,known
    for m in records:
        if m.before_generation!=version or m.after_generation!=version+1:
            return None
        if m.reverse:placement=placement[::-1]
        version=m.after_generation
    return placement if version==target else None
