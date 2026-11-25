"""Physical effect discovery for pending predecessor and successor duties."""
from dataclasses import dataclass,field
from collections import defaultdict
from random import Random

@dataclass
class PhysicalRole:
    current:int
    version:int=0
    prepare_to:int|None=None
    progress:int=0
    tail:dict[int,int]=field(default_factory=dict) # token -> actual unsettled old helper

class Plant:
    def __init__(self,R):
        self.R=dict((i,PhysicalRole(x)) for i,x in enumerate(R))
        self.next_token=0
        self.watermark=0

    def prepare(self,j,r):
        q=self.R[j]
        assert q.prepare_to is None and q.current!=r
        q.prepare_to=r;q.progress=0

    def support_tick(self,j,physical_action_completed):
        q=self.R[j]
        assert q.prepare_to is not None
        q.progress=q.progress+1 if physical_action_completed else 0
        if q.progress!=2:return None
        old=q.current;now=q.prepare_to
        self.next_token+=1
        k=self.next_token
        q.tail[k]=old
        q.current=now
        q.prepare_to=None;q.progress=0
        q.version+=1
        self.watermark+=1
        return self.watermark,"mate",j,k,old,now

    def actual_settle(self,j,token,owned_completion):
        q=self.R[j]
        if token not in q.tail or not owned_completion:return None
        old=q.tail.pop(token)
        self.watermark+=1
        return self.watermark,"retire",j,token,old,0

    def affected(self,helper):
        return {i for i,q in self.R.items()
                if q.current==helper or helper in q.tail.values()}

class Validator:
    def __init__(self,R):
        self.index=defaultdict(dict)
        self.watermark=0
        self.current=dict(enumerate(R))
        self.tails={}
        self.writes=0
        for i,r in self.current.items():self.amend(i,r,1)

    def amend(self,j,r,d):
        old=self.index[r].get(j,0)
        assert old+d>=0
        if old+d:self.index[r][j]=old+d
        else:del self.index[r][j]
        self.writes+=1

    def accept(self,row):
        k,op,j,token,old,new=row
        if k!=self.watermark+1:return False
        if op=="mate":
            assert self.current[j]==old and (j,token) not in self.tails
            # The old edge already exists and now marks an actual retained
            # tail. It remains a proving read until its specific settlement.
            self.tails[j,token]=old
            self.current[j]=new;self.amend(j,new,1)
        elif op=="retire":
            assert self.tails.pop((j,token))==old
            self.amend(j,old,-1)
        else:raise ValueError(op)
        self.watermark=k
        return True

    def read(self,helper,certified_through):
        if self.watermark<certified_through:return None
        return set(self.index[helper])

def controls():
    plant=Plant([0,3]);V=Validator([0,3])
    plant.prepare(0,1)
    assert plant.support_tick(0,True) is None
    assert plant.support_tick(0,False) is None
    assert V.read(1,0)==set()
    assert plant.support_tick(0,True) is None
    withhold=plant.support_tick(0,True)
    assert V.read(1,plant.watermark) is None
    assert V.accept(withhold)
    assert V.read(1,1)==V.read(0,1)=={0}
    # Return to old source while that very predecessor effect is still
    # active. Its separate record cannot be erased with "latest epoch".
    plant.prepare(0,0)
    assert plant.support_tick(0,True) is None
    assert V.accept(plant.support_tick(0,True))
    assert V.accept(plant.actual_settle(0,withhold[3],True))
    assert V.read(0,plant.watermark)=={0}
    assert V.read(1,plant.watermark)=={0}
    assert V.accept(plant.actual_settle(0,withhold[3]+1,True))
    assert V.read(1,plant.watermark)==set()
    # A second still-active duty retains its own source control.
    assert V.read(3,plant.watermark)=={1}
    print("real move changes the active producer; the old held effect does not retire")
    print("late source stream refuses release; return to the same producer keeps its current edge")

def tests():
    rng=Random(251239);n=200
    S=[rng.randrange(20) for _ in range(n)]
    plant=Plant(S);V=Validator(S)
    rows=queries=0
    for tick in range(4000):
        i=rng.randrange(n);q=plant.R[i]
        if q.prepare_to is not None:
            event=plant.support_tick(i,rng.randrange(4)!=0)
        elif q.tail and rng.randrange(2):
            event=plant.actual_settle(i,min(q.tail),rng.randrange(4)!=0)
        else:
            r=rng.randrange(20)
            if r!=q.current:plant.prepare(i,r)
            event=None
        if event:
            before=V.writes
            assert V.accept(event)
            assert V.writes==before+1
            assert not V.accept(event)  # no falsely repeated retire
            rows+=1
        for _ in range(2):
            r=rng.randrange(20)
            assert V.read(r,plant.watermark)==plant.affected(r)
            queries+=1
    print(rows,"measured source event steps, one reverse-index edit apiece")
    print(queries,"indexed/full source dependencies match under 4000 physical transitions")
if __name__=="__main__":controls();tests()
