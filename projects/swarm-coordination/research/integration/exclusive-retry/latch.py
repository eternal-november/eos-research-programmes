"""A simulated effect-side latch is not a software lease."""
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class Grant:
    scope: str
    round: int
    key: str

class Latch:
    def __init__(self,scope='one settlement'):
        self.scope=scope;self.epoch=0;self.active=None;self.done=None;self.trace=[]
    def request(self,time,g,physically_ready,fail,drain,serve):
        if self.done is not None or self.active is not None:return False
        if (g.scope,g.round)!=(self.scope,self.epoch) or not physically_ready:return False
        self.active=(g.key,g.round,time+(drain if fail else serve),fail)
        self.trace.append((time,"held",g.key,g.round))
        return True
    def cancel_status(self,t):
        self.trace.append((t,"cancel-request",None,None))
    def finish(self,t,scope,epoch,observed_effect):
        if self.active is None or scope!=self.scope:return False
        key,gen,done,fail=self.active
        if epoch!=gen or t<done or observed_effect!=("physically-clear-no-effect" if fail else "effect-settled"):return False
        self.active=None;self.epoch+=1
        self.trace.append((t,observed_effect,key,gen))
        if not fail:self.done=(t,key,gen)
        return True

def main():
    c=0
    for ra,rb,fail_a,delay in product((False,True),(False,True),(False,True),range(1,8)):
        a=Latch();scope=a.scope
        akey,bkey=Grant(scope,0,"A"),Grant(scope,0,"B")
        first=a.request(0,akey,ra,fail_a,delay,2)
        second=a.request(0,bkey,rb,False,1,2)
        assert first+second==int(ra or rb)
        if first or second:
            old=a.active
            a.cancel_status(1)
            assert a.active==old and not a.request(1,bkey,rb,False,delay,2)
            key,g,t,fail=old
            rec="physically-clear-no-effect" if fail else "effect-settled"
            assert not a.finish(t-1,scope,g,rec)
            assert not a.finish(t,'wrong',g,rec)
            assert not a.finish(t,scope,g+1,rec)
            assert a.finish(t,scope,g,rec)
            assert not a.request(t,bkey,rb,False,delay,2)
            if fail and rb:
                assert a.request(t,Grant(scope,1,"B"),True,False,delay,2)
                assert a.finish(t+2,scope,1,"effect-settled")
            else:
                assert not a.request(t,Grant(scope,1,"B"),rb,False,delay,2)
            assert len([1 for _,e,_,_ in a.trace if e=="effect-settled"])<=1
        c+=1
    print(c,'overlapping grants, logical cancellation, stale and wrong-scope attestations checked')
if __name__=='__main__':main()
