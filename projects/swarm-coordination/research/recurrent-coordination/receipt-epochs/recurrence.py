"""Finite per-edge controls, asynchronous two-ended witnesses and real custody."""
from dataclasses import dataclass,field
from random import Random
from itertools import product
from alternating import colour

@dataclass(frozen=True)
class Packet:
    # Actual emitted g is carried by the verifier model, not a wire field.
    scope: int
    signer: int
    tag: int
    g: int

@dataclass
class Edge:
    left: int
    hand: int # verifier integer real count; gate data below are bounded
    who: int  # actual old custodian endpoint index, 0 or 1
    tag: int
    phase: str = 'empty'
    source_ready: bool=False # physically witnessed by the old holder only
    left_saw: bool=False
    right_saw: bool=False
    packets: list=field(default_factory=list) # unbounded environment only
    ages: list=field(default_factory=list) # bounded physical queue slots

class Chain:
    def __init__(self,n,L,aging=True):
        assert n>=2
        self.L=L;self.module=L//2+1;self.aging=aging
        self.e=[Edge(i,0,i%2,0,ages=[None]*(L+1)) for i in range(n-1)]
        self.queue=[[] for i in range(n)]
        self.max_queue=0;self.commits=[0]*(n-1);self.rejects=0;self.custody_swaps=0
    def offer(self,i):
        e=self.e[i]
        if e.phase!='empty':return False
        e.phase='carry';e.source_ready=False
        return True
    def witnessed_clearance(self,i):
        # The physical old hold on the source apparatus clears, while old
        # custody duty still belongs to the original party until actual commit.
        e=self.e[i]
        if e.phase!='carry' or e.source_ready:return False
        e.source_ready=True
        packet=Packet(i,e.who,e.tag,e.hand)
        if self.aging:e.ages[0]=packet
        else:e.packets.append(packet)
        return True
    def candidate(self,i,p):
        e=self.e[i]
        # Local receiver consumes only fixed scope, principal, tag and
        # actual phase/duplicate exclusion. Absolute generation is not read.
        if (p.scope,p.signer,p.tag)!=(i,e.who,e.tag) or e.phase!='carry':
            self.rejects+=1;return False
        # Verifier records real authenticated provenance, not runtime fact.
        assert p.g==e.hand and e.source_ready
        target=e.left+(1-e.who)
        assert i not in self.queue[target]
        self.queue[target].append(i)
        self.max_queue=max(self.max_queue,len(self.queue[target]))
        e.phase='queued'
        return True
    def serve(self,s):
        if not self.queue[s]:return False
        i=self.queue[s].pop(0)
        e=self.e[i]
        assert e.phase=='queued' and s==e.left+1-e.who and e.source_ready
        # This is the modeled irreversible custody event; only this changes
        # who can provide the next actual clearance, not the packet receipt.
        e.who^=1;e.phase='observing'
        self.custody_swaps+=1
        e.left_saw=e.right_saw=False
        self.commits[i]+=1
        return True
    def see(self,i,p):
        e=self.e[i]
        if e.phase!='observing':return False
        if (e.left_saw,e.right_saw)[p]:return False
        if p==0:e.left_saw=True
        else:e.right_saw=True
        # A physically shared edge gate reopens only after independent
        # local reads are witnessed. No global observation or clock.
        if e.left_saw and e.right_saw:
            e.phase='empty';e.hand+=1
            if e.who==(i%2):e.tag=(e.tag+1)%self.module
            assert e.tag==colour(e.hand,self.L)
            if self.aging:
                # Bounded physical relay: shift buckets only on the local
                # completed handoff; rewind/reconstruction is not permitted.
                e.ages=[None]+e.ages[:-1]
        return True
    def assert_state(self):
        for s,Q in enumerate(self.queue):
            assert len(Q)<=2 and len(set(Q))==len(Q)
            for i in Q:
                assert self.e[i].phase=='queued'
                assert self.e[i].left+(1-self.e[i].who)==s
        for i,e in enumerate(self.e):
            assert e.who==(i+ self.commits[i])%2
            assert all(p.g<=e.hand for p in e.packets)
            if self.aging:
                assert len(e.ages)==self.L+1
                assert all(p is None or e.hand-p.g==age for age,p in enumerate(e.ages))
            assert (e.phase=='queued')==any(i in Q for Q in self.queue)
            assert sum(i in Q for Q in self.queue)<=1

def pulse(c,rng):
    # Actual actions may interleave arbitrarily; every offered source
    # is helped once per sweep here (a deterministic fairness fixture).
    es=list(range(len(c.e)));rng.shuffle(es)
    for i in es:
        e=c.e[i]
        if e.phase=='empty':c.offer(i)
        elif e.phase=='carry':
            if not e.source_ready:c.witnessed_clearance(i)
            else:
                ps=([p for p in e.ages if p is not None] if c.aging else e.packets.copy());rng.shuffle(ps)
                for p in ps:c.candidate(i,p)
        elif e.phase=='observing':
            for p in (rng.randrange(2),0,1):c.see(i,p)
    stations=list(range(len(c.queue)));rng.shuffle(stations)
    for s in stations:
        c.serve(s)
    c.assert_state()

def main():
    nchecks=0
    for L,n in product(range(8),(2,3,4,7,16,33)):
        C=Chain(n,L)
        r=Random(n*113+L)
        for q in range(350):
            pulse(C,r)
        assert all(k>=80 for k in C.commits)
        if n>=3:assert C.max_queue==2
        nchecks+=sum(C.commits)
    print(nchecks,'repeated civil custody changes, arbitrary interface sizes in the tested family')
    # Withhold a real current clearance just after a complete same-authority
    # tag cycle, and let an indistinguishable old receipt reappear.
    L=4;C=Chain(2,L,aging=False)
    C.offer(0);C.witnessed_clearance(0);old=C.e[0].packets[0]
    for g in range(2*C.module):
        e=C.e[0]
        if e.phase=='empty':C.offer(0);C.witnessed_clearance(0)
        assert C.candidate(0,e.packets[-1])
        C.serve(1-e.who)
        C.see(0,0);C.see(0,1)
    assert C.offer(0)
    try:
        C.candidate(0,old)
    except AssertionError:
        print('unbounded age permits authorized old-signature alias before the new physical clearance')
    else:
        raise AssertionError('stale alias was not detected')
if __name__=='__main__':main()
