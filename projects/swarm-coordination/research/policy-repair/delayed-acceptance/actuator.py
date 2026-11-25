"""Physical correspondence for a small prerecorded gate/custody source."""
from dataclasses import dataclass
from solve import compile_rule

@dataclass(frozen=True)
class Plant:
    physical_acceptance: int
    packet_latency: int
    support_after_acceptance: int = 4
    minimum_setup: int = 1
    positive_transfer: int = 2

    def active(self,t):
        return self.physical_acceptance<=t<self.physical_acceptance+self.support_after_acceptance

    def commit_if_ready(self,start):
        # No command or receipt sets accepted custody. The original support
        # must actually remain present on every transfer tick and the next
        # carrier may settle only after the complete overlap. The contract
        # imposes one tick of pre-start physical preparation.
        ca=self.physical_acceptance
        return all(self.active(t) for t in range(start-self.minimum_setup,start+self.positive_transfer))

    def abstract(self,stamp):
        ca=self.physical_acceptance
        return (ca+self.minimum_setup,ca+self.support_after_acceptance-self.positive_transfer,
                ca+self.packet_latency,ca if stamp else 0)

def closed_loop(worlds,stamp):
    rows=[w.abstract(stamp) for w in worlds]
    policy=compile_rule(rows)
    if policy is False:return False
    s,sub=policy
    for plant,(a,b,r,y) in zip(worlds,rows):
        got=None
        candidate=None
        for tick in range(max(b,r)+1):
            if tick==r:
                got=(r,y)
                if got in sub:candidate=sub[got]
            if (got is None and tick==s) or tick==candidate:
                assert plant.commit_if_ready(tick)
                break
        else:raise AssertionError((plant,policy))
    return True

if __name__=="__main__":
    n=0
    for c in range(6):
        for d in range(6):
            for width in range(3,8):
                w=Plant(c,d,width)
                lo,hi,*_=w.abstract(True)
                assert all(w.commit_if_ready(t)==(lo<=t<=hi) for t in range(15))
                n+=15
    print(n,"physical trace/window matches")
    assert closed_loop([Plant(0,2),Plant(2,0)],True)
    assert not closed_loop([Plant(0,2),Plant(2,0)],False)
    assert closed_loop([Plant(0,0),Plant(3,5)],False)
    print("same actuator source, same delay, distinct timestamp outcomes; late packet hybrid succeeds")
