"""Exact lag-one ladder semantics and width-two relational inference.

Integers represent twice the physical load. Prior graph is a supplied ladder;
actual parent selectors are hidden, static, and never supplied to the planner.
"""
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from collections import defaultdict
from exact_search import Step, WIN, LOSE

@dataclass(frozen=True)
class Job:
    release:int
    deadline:int
    routes:tuple

@dataclass(frozen=True)
class State:
    t:int
    energy:int
    previous:tuple
    progress:tuple  # (chosen route or -1, completed stages)
    domains:tuple   # bit masks in each node's parent-choice list

@dataclass(frozen=True)
class Action:
    controls:tuple
    credits:tuple  # route index per job, -1 for no credited stage

class LadderInference:
    def __init__(self,n):
        assert n>=2 and n%2==0
        self.n=n;self.m=n//2
        self.choices=tuple(tuple([-1]+sorted(set([i^1]+([i-2] if i>=2 else [])+([i+2] if i+2<n else [])))) for i in range(n))
        self.stats=defaultdict(int)
        self.support=lru_cache(maxsize=None)(self._support)
        self.outcomes=lru_cache(maxsize=None)(self._outcomes)

    def initial(self):return tuple((1<<len(c))-1 for c in self.choices)
    def values(self,i,mask):return tuple(p for b,p in enumerate(self.choices[i]) if mask>>b&1)
    def mask(self,i,values):
        return sum(1<<b for b,p in enumerate(self.choices[i]) if p in values)
    def pairs(self,domains,col):
        i=2*col
        return tuple((p,q) for p in self.values(i,domains[i]) for q in self.values(i+1,domains[i+1]) if not(p==i+1 and q==i))
    def compatible(self,left,right,col):
        # left is column col-1, right is column col
        i=2*col
        return all(not(left[r]==i+r and right[r]==i-2+r) for r in (0,1))

    def _support(self,domains):
        self.stats['support_queries_uncached']+=1
        pairs=[self.pairs(domains,c) for c in range(self.m)]
        forward=[set(pairs[0])]
        for c in range(1,self.m):
            s=set()
            for q in pairs[c]:
                for p in forward[-1]:
                    self.stats['separator_pair_tests']+=1
                    if self.compatible(p,q,c):s.add(q);break
            forward.append(s)
        if not forward[-1]:return None
        backward=[None]*self.m;backward[-1]=forward[-1]
        for c in range(self.m-2,-1,-1):
            s=set()
            for p in forward[c]:
                for q in backward[c+1]:
                    self.stats['separator_pair_tests']+=1
                    if self.compatible(p,q,c+1):s.add(p);break
            backward[c]=s
        result=[]
        for c,ps in enumerate(backward):
            result.extend(self.mask(2*c+r,{p[r] for p in ps}) for r in (0,1))
        return tuple(result)

    def _outcomes(self,domains,previous):
        """Feasible joint previous-input labels via a width-two frontier.

        The prefix observation is retained. Different feasible frontier pairs
        with the same prefix are merged, never independently cross-multiplied.
        """
        self.stats['outcome_queries_uncached']+=1
        def obs(pair):return tuple(0 if p<0 else previous[p] for p in pair)
        groups=defaultdict(set)
        for p in self.pairs(domains,0):groups[obs(p)].add(p)
        for c in range(1,self.m):
            nxt=defaultdict(set)
            for prefix,front in groups.items():
                for q in self.pairs(domains,c):
                    feasible=False
                    for p in front:
                        self.stats['outcome_separator_tests']+=1
                        if self.compatible(p,q,c):feasible=True;break
                    if feasible:nxt[prefix+obs(q)].add(q)
            groups=nxt
        answer=[]
        for observation in sorted(groups):
            masks=tuple(self.mask(i,{p for p in self.values(i,domains[i]) if (0 if p<0 else previous[p])==observation[i]}) for i in range(self.n))
            supported=self.support(masks)
            assert supported is not None
            answer.append((observation,supported))
        self.stats['joint_outcomes_emitted']+=len(answer)
        return tuple(answer)

    def complete_worlds(self,domains):
        """Diagnostic/reference enumeration, never needed by symbolic planner."""
        def rec(col,prefix,last):
            if col==self.m:
                yield prefix;return
            for p in self.pairs(domains,col):
                if col==0 or self.compatible(last,p,col):
                    yield from rec(col+1,prefix+p,p)
        yield from rec(0,(),None)

class LadderModel:
    def __init__(self,n,jobs,power,energy,checker='local',frozen=False):
        self.n=n;self.jobs=tuple(jobs);self.power=power;self.energy=energy
        self.inf=LadderInference(n);self.checker=checker;self.frozen=frozen
        self.stats=defaultdict(int)
        self.controls=tuple(u for u in product(range(3),repeat=n) if sum(u)<=power)
    def initial(self):
        return State(0,self.energy,(0,)*self.n,tuple((-1,0) for j in self.jobs),self.inf.initial())
    def encode_state(self,s):return [s.t,s.energy,list(s.previous),[list(x) for x in s.progress],list(s.domains)]
    def decode_state(self,x):return State(x[0],x[1],tuple(x[2]),tuple(map(tuple,x[3])),tuple(x[4]))
    def encode_action(self,a):return [list(a.controls),list(a.credits)]
    def encode_observation(self,o):return list(o)
    def remaining(self,s):
        return tuple((len(j.routes[r]) if r>=0 else min(map(len,j.routes)))-done for j,(r,done) in zip(self.jobs,s.progress))
    def terminal(self,s):
        remaining=self.remaining(s)
        if any(k and s.t>j.deadline for k,j in zip(remaining,self.jobs)):
            return LOSE,'deadline_missing_stage'
        if 2*sum(remaining)>s.energy:return LOSE,'insufficient_productive_energy'
        if any(k and k>j.deadline-max(s.t,j.release)+1 for k,j in zip(remaining,self.jobs)):
            return LOSE,'insufficient_sequential_slots'
        if not any(remaining) and not any(s.previous):return WIN,'mission_complete_and_tail_cleared'
        if s.t>max(j.deadline for j in self.jobs)+1:return LOSE,'horizon_exhausted'
        return None
    def actions(self,s):
        remaining=self.remaining(s);ranked=[]
        for u in self.controls:
            cost=sum(u)
            if cost>s.energy:continue
            options=[]
            for j,(r,done),rem in zip(self.jobs,s.progress,remaining):
                opts=[(-1,-1)]
                if rem and j.release<=s.t<=j.deadline:
                    routes=range(len(j.routes)) if r<0 else (r,)
                    for k in routes:
                        node=j.routes[k][done]
                        if u[node]==2:opts.append((k,node))
                options.append(opts)
            for assignment in product(*options):
                used=[v for _,v in assignment if v>=0]
                if len(used)!=len(set(used)):continue
                credits=tuple(k for k,_ in assignment)
                progress=len(used)
                urgency=sum(1/(1+j.deadline-s.t) for j,(k,_) in zip(self.jobs,assignment) if k>=0)
                # Pure ordering heuristic, all controls/credits remain available.
                informative=sum(u[i]>0 and any(mask&(mask-1) for mask in (s.domains[v] for v in range(self.n) if i in self.inf.choices[v])) for i in range(self.n))
                score=(-progress,-urgency,cost-progress*2,-informative,u,credits)
                ranked.append((score,Action(u,credits)))
        ranked.sort(key=lambda z:z[0])
        return tuple(a for _,a in ranked)
    def transition(self,s,a):
        u=a.controls; support=self.inf.support(s.domains)
        assert support is not None
        rows=range(self.n) if self.checker=='full_scope' else (i for i in range(self.n) if u[i]==2)
        for i in rows:
            self.stats['physical_rows_checked']+=1
            for parent in self.inf.values(i,support[i]):
                self.stats['parent_values_checked']+=1
                load=u[i]+(0 if parent<0 else s.previous[parent])
                if load>3:return Step(unsafe=dict(node=i,parent=parent,twice_load=load))
        progress=tuple((r,done) if k<0 else (k,done+1) for (r,done),k in zip(s.progress,a.credits))
        if self.frozen:
            # Ignored observations: one abstract branch preserves prior evidence.
            return Step(outcomes=(((),State(s.t+1,s.energy-sum(u),u,progress,s.domains)),))
        results=[]
        for delayed,domains in self.inf.outcomes(s.domains,s.previous):
            observation=tuple(u[i]+delayed[i] for i in range(self.n))
            results.append((observation,State(s.t+1,s.energy-sum(u),u,progress,domains)))
        return Step(outcomes=tuple(results))
