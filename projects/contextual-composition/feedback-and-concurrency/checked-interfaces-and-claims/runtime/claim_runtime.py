"""Scoped claim-right extension. Administrative issuance is not primitive minting.
Trusted typed clients use static slot indices; public handles are not claim rights.
"""
import sys
from pathlib import Path
from ordered_runtime import *

@dataclass(frozen=True)
class ClaimSpawn:
    term: Any
    child_slots: tuple[int,...]
    result_interface: str

@dataclass(frozen=True)
class ClaimAwait:
    ticket_slot: int

class ClaimMachine(OrderedMachine):
    JOIN='@join-claim'
    def __init__(self,*args,**kwargs):
        self.claim_rights={};self.next_claim=0
        if self.JOIN in (kwargs.get('kinds') or {}).values():
            raise ValueError('initial claim rights require a separately declared configuration')
        super().__init__(*args,**kwargs)

    def ticket(self,pid,slot):
        held=self.owned(('job',pid))
        if type(slot)!=int or not 0<=slot<len(held):return None
        cap=held[slot]
        return cap if cap in self.claim_rights and self.kinds[cap]==self.JOIN else None

    def enabled(self):
        ready=super().enabled()
        out=[]
        for pid in ready:
            t=self.jobs[pid].term
            if self.jobs[pid].mode=='eval' and isinstance(t,ClaimAwait):
                cap=self.ticket(pid,t.ticket_slot)
                if cap is not None:
                    h,_=self.claim_rights[cap]
                    if self.jobs[h].mode!='done':continue
            out.append(pid)
        return out

    def validate_outcome(self,pid,o):
        super().validate_outcome(pid,o)
        if any(k==self.JOIN for k in o.mint.values()) or any(k==self.JOIN for k in o.retype.values()):
            raise ValueError('primitive cannot manufacture join rights')
        held_rights=set(self.owned(('job',pid)))&set(self.claim_rights)
        if held_rights & (set(o.consume)|set(o.retype)):
            raise ValueError('claim right can be consumed only by claim-await')
        if any(c in o.stores and o.stores[c]!=self.stores[c] for c in held_rights):
            raise ValueError('primitive cannot change claim target')

    def step(self,pid,**choices):
        j=self.jobs[pid]
        if j.mode!='eval':return super().step(pid,**choices)
        t=j.term;held=self.owned(('job',pid))
        if isinstance(t,Await):raise ValueError('bare public-handle await outside claim-right model')
        if isinstance(t,ClaimSpawn):
            ids=t.child_slots
            if len(ids)!=len(set(ids)) or any(type(i)!=int or not 0<=i<len(held) for i in ids):
                raise ValueError('invalid child slot partition')
            cs=tuple(held[i] for i in ids)
            cap=f'@claim:{self.next_claim}'
            while cap in self.ledger:
                self.next_claim+=1;cap=f'@claim:{self.next_claim}'
            # No primitive outcomes are enumerated here: this is one committed administrative issue.
            h=self.new_job(t.term,j.value,cs,('job',pid),(self.next_job,),None)
            self.next_claim+=1
            self.claim_rights[cap]=(h,t.result_interface)
            self.ledger[cap]=('job',pid);self.kinds[cap]=self.JOIN;self.stores[cap]=h
            self.interface_order['job',pid]=self.owned(('job',pid))+(cap,)
            self.trace.append(('claim-spawn',pid,h,cap,t.result_interface))
            self.finish(pid,Result(Leaf(h,self.owned(('job',pid))),('claim-spawn',h,cap)))
        elif isinstance(t,ClaimAwait):
            cap=self.ticket(pid,t.ticket_slot)
            if cap is None:
                self.finish(pid,Result(Leaf({'refused':'missing claim right'},held),('claim-await-refused',)))
            else:
                h,q=self.claim_rights[cap]
                if self.jobs[h].mode!='done':return False
                r=self.claim(h,pid)
                self.ledger[cap]=('retired',cap)
                self.interface_order['job',pid]=tuple(c for c in self.owned(('job',pid)) if c!=cap)
                reserve=tuple(c for c in held if c!=cap)
                tree=Node('Fork',(r.tree,Leaf(j.value,reserve)),True)
                self.trace.append(('claim-await',pid,h,cap,q))
                self.finish(pid,Result(tree,('claim-await',h,cap,r.raw),r.events,r.status))
        else:return super().step(pid,**choices)
        self.assert_invariant();return True

    def assert_invariant(self):
        super().assert_invariant()
        targets=[]
        for cap,(h,q) in self.claim_rights.items():
            assert h in self.jobs and self.kinds[cap]==self.JOIN and self.stores[cap]==h
            assert self.jobs[h].parent is None
            targets.append(h)
            retired=self.ledger[cap][0]=='retired'
            assert retired==self.jobs[h].claimed
        assert len(targets)==len(set(targets))
        assert all(c in self.claim_rights for c,k in self.kinds.items() if k==self.JOIN)
