"""Finite authorization and scoped consent for an installation with sealed names."""
from dataclasses import dataclass
from itertools import combinations

def subsets(xs):
    for i in range(1,len(xs)+1):
        yield from combinations(xs,i)

def hall_lower(allowed):
    def needed(U):
        g=len(set().union(*(allowed[j] for j in U)))
        if not g:
            return None
        return (len(U)+g-1)//g
    values=[needed(u) for u in subsets(tuple(range(len(allowed))))]
    return None if None in values else max(values,default=0)

def assign(allowed, cap):
    # Matching to repeated named hint slots. Slot numbers are not advertised.
    owner={}
    def push(j,visited):
        for h in sorted(allowed[j]):
            for i in range(cap):
                slot=h,i
                if slot in visited:
                    continue
                visited.add(slot)
                if slot not in owner or push(owner[slot],visited):
                    owner[slot]=j
                    return True
        return False
    if not all(push(j,set()) for j in range(len(allowed))):
        return None
    hint={j:h for (h,_),j in owner.items()}
    return tuple(hint[j] for j in range(len(allowed)))

@dataclass(frozen=True)
class Charter:
    revision: int
    roster: tuple # stable ordering of bay names in each hint
    # Privacy scope is validated by source admission, not by this dataclass.

@dataclass(frozen=True)
class Reply:
    epoch: int
    revision: int
    hint: int
    bits: tuple

def reply(charter,epoch,hint,can):
    return Reply(epoch,charter.revision,hint,tuple(can[j] for j in charter.roster[hint]))

def locally_admit(charter,expected_epoch,j,hint,record):
    if record is None or not (0<=hint<len(charter.roster)):
        return False
    bucket=charter.roster[hint]
    if (record.epoch,record.revision,record.hint)!=(expected_epoch,charter.revision,hint):
        return False
    if j not in bucket or len(record.bits)!=len(bucket):
        return False
    return bool(record.bits[bucket.index(j)])

@dataclass
class Effect:
    epoch: int
    charter: Charter
    actual_assent: tuple
    holders: list
    blockage: tuple
    at: list  # each bay's load initially at its local pickup
    next_permits: list
    old_at: str = 'separate-origin'

    def serve_old(self):
        if self.old_at != 'separate-origin':
            return False
        self.old_at='separate-destination'
        return True

    def can_amend(self,actor,j):
        return self.holders[j]==actor

    def schedule_next(self,actor,j,variant):
        if not self.can_amend(actor,j) or self.at[j]!='receiving-bay':
            return False
        if self.next_permits[j] is not None or variant not in ('inspect','egress'):
            return False
        self.next_permits[j]=variant
        return True

    def commit(self,record,j,hint):
        # A's local enforcer rechecks actual scope and assent at its effect.
        if not locally_admit(self.charter,self.epoch,j,hint,record):
            return False
        if not self.actual_assent[j] or self.holders[j]!='A':
            return False
        if self.blockage[j] or self.at[j]!='pickup':
            return False
        self.at[j]='receiving-bay'
        self.holders[j]='B'
        return True
