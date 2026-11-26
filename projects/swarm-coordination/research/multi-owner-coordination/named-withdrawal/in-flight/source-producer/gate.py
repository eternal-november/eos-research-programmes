from dataclasses import dataclass

@dataclass(frozen=True)
class ScopeRead:
    epoch: int
    phase: int
    pending: frozenset

@dataclass(frozen=True)
class Op:
    actor: int
    action: object
    before: tuple[int,int]
    after: tuple[int,int]
    holds_before: str | None
    holds_after: str | None
    def footprint(self):
        cells={("cell",*self.before),("cell",*self.after)}
        assets={("asset",n) for n in (self.holds_before,self.holds_after) if n is not None}
        return frozenset(cells|assets|{("actor",self.actor)})

def footprint(tape):
    return frozenset().union(*(a.footprint() for a in tape))

class Gate:
    def __init__(self,tape):
        self.epoch=0
        self.phase=0
        self.tape=tuple(tape)
        self.claim=None
        self.scope_reads=0
        self.commands_verified=0
        self.edits_checked=0
    def read(self):
        self.scope_reads+=len(self.tape)
        return ScopeRead(self.epoch,self.phase,footprint(self.tape))
    def acquire(self,read,new):
        # Consumer normally uses the command footprint of a qualified local job.
        actual=self.read()
        if read!=actual or self.claim is not None or new&actual.pending:
            return False
        self.claim=frozenset(new)
        return True
    def edit(self,tape):
        self.edits_checked+=len(tape)
        if self.claim is not None and self.claim&footprint(tape):
            return False
        self.tape=tuple(tape)
        self.epoch+=1
        return True
    def mark(self,op,before,after):
        assert self.tape and self.tape[0]==op
        assert before==(op.before,op.holds_before) and after==(op.after,op.holds_after)
        self.commands_verified+=1
        self.phase+=1
        self.tape=self.tape[1:]
    def release(self,completed):
        assert self.claim is not None
        if not completed:return False
        self.claim=None
        return True
