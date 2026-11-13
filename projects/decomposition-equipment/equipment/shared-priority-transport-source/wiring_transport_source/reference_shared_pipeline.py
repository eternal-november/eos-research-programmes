"""Executable local-work -> acquired shared-priority -> anonymous parity transport.
No old pipeline imports. Simulator truth is used only by the test oracle. Public
reports have exactly (time, bit); priorities, job IDs and grants are not exposed.
All time units are integer ticks. Budget constants are supplied interface bounds,
not empirical claims about Python runtime or a physical actuator.
"""
from dataclasses import dataclass
from collections import deque
import heapq
import itertools
import json
import math
import random
from pathlib import Path
from poset_parity_checker import certify, closure
from poset_parity_verifier import verify


@dataclass(frozen=True)
class Request:
    module: int
    operation: str                 # P useful work Q; D safe diagnostic work 2Q
    useful: bool = False


@dataclass(frozen=True)
class PublicCaps:
    n: int
    work_upper: int
    R: int
    J: int


class Plant:
    """One persistent nonpreemptive work-conserving priority arbiter.

    Never clear/reset the running job or queues between experiments. Every
    batch is inserted in its entirety before any idle dispatch at that tick.
    _truth_* and private priority exist solely for simulation/validation.
    """
    def __init__(self, priority, Q=100, R=None, J=0, seed=0, payloads=None, lags=None, caps=None):
        self.n = len(priority)
        assert sorted(priority) == list(range(self.n))
        self.caps = caps or PublicCaps(self.n, 100, R or self.n * 100, J)
        assert 0 < Q <= self.caps.work_upper and self.n == self.caps.n
        self.__Q, self.R, self.J = Q, self.caps.R, self.caps.J
        self.__priority = tuple(priority)
        self.__queues = [deque() for _ in priority]
        self.__running = None
        self.__callbacks = []
        self.__counter = 0
        self.__last_commit = None
        self.__rng = random.Random(seed)
        self.__payloads = iter(payloads) if payloads is not None else None
        self.__lags = iter(lags) if lags is not None else None
        self.now = 0
        self.raw = []
        self._truth_jobs = []
        self._truth_service = []

    def _dispatch(self):
        if self.__running is not None:
            return
        for module in self.__priority:
            if self.__queues[module]:
                job = self.__queues[module].popleft()
                job['start'] = self.now
                job['finish'] = self.now + job['demand']
                self.__running = job
                self._truth_service.append(job)
                return

    def advance(self, t, dispatch_endpoint=True):
        if t < self.now:
            raise ValueError('cannot rewind persistent server')
        while True:
            finish = self.__running['finish'] if self.__running else math.inf
            callback = self.__callbacks[0][0] if self.__callbacks else math.inf
            event = min(finish, callback)
            if event > t:
                break
            self.now = event
            if finish == event:
                job = self.__running
                self.__running = None
                heapq.heappush(self.__callbacks, (event + job['lag'], job['index'], job['bit']))
            while self.__callbacks and self.__callbacks[0][0] <= event:
                when, _, bit = heapq.heappop(self.__callbacks)
                self.raw.append((when, bit))
            if event < t or dispatch_endpoint:
                self._dispatch()
            # endpoint with dispatch withheld: no zero-work or hidden reset
            if event == t:
                break
        self.now = t
        if dispatch_endpoint:
            self._dispatch()

    def admit_batch(self, t, requests):
        if t % self.R:
            raise ValueError('off admission grid')
        if t < self.now:
            raise ValueError('late batch')
        if t == self.__last_commit:
            raise ValueError('only one atomic batch commit per admission tick')
        requests = list(requests)
        if any(not 0 <= r.module < self.n or r.operation not in ('P', 'D') for r in requests):
            raise ValueError('invalid request')
        self.advance(t, dispatch_endpoint=False)
        self.__last_commit = t  # even an empty commit consumes the tick
        for r in requests:
            bit = next(self.__payloads) if self.__payloads is not None else self.__rng.randrange(2)
            lag = next(self.__lags) if self.__lags is not None else self.__rng.randrange(self.J+1)
            if bit not in (0, 1) or not 0 <= lag <= self.J:
                raise ValueError('invalid physical bit/lag')
            job = dict(index=self.__counter, module=r.module, operation=r.operation,
                       useful=r.useful, release=t, demand=self.__Q*(1+(r.operation=='D')),
                       bit=bit, lag=lag)
            self.__counter += 1
            self.__queues[r.module].append(job)
            self._truth_jobs.append(job)
        self._dispatch()

    def _truth_empty(self):
        # Test oracle only; controllers derive drain from public upper horizons.
        return self.__running is None and not any(self.__queues) and not self.__callbacks


def ceilgrid(t, R):
    return R * ((t + R - 1)//R)


@dataclass(frozen=True)
class Budget:
    init: int = 7
    probe_handling: int = 5
    probe_tail: int = 3
    compile: int = 10
    runtime: int = 8
    mission_tail: int = 4
    gamma: int = 20


def envelope(n, Q, R, b, comparison_bound=None):
    m = n * math.ceil(math.log2(n)) if comparison_bound is None else comparison_bound
    local = n * (ceilgrid(Q+b.probe_handling+b.probe_tail,R) +
                 ceilgrid(2*Q+b.probe_handling+b.probe_tail,R))
    joint = ceilgrid(b.init,R) + m*ceilgrid(3*Q+b.probe_handling+b.probe_tail,R) + ceilgrid(b.compile,R)
    return dict(local=local, joint=joint, comparison_bound=m, T0=local+joint, deadline=local+joint+n*Q+b.gamma,
                max_invocations=2*n+2*m+n)


class Learner:
    def __init__(self, plant, budget, caps):
        self.p, self.b, self.c = plant, budget, caps
        self.local = {}
        self.edges = []
        self.comparisons = []
        self.cost = dict(local_invocations=0, joint_invocations=0, reserved_probe_horizon=0,
                         handling=0, probe_tails=0, grid_idle=0, initial=budget.init,
                         compile=0)
        plant.advance(budget.init)

    def _probe(self, requests, horizon):
        start = ceilgrid(self.p.now, self.c.R)
        self.cost['grid_idle'] += start-self.p.now
        begin = len(self.p.raw)
        self.p.admit_batch(start, requests)
        self.p.advance(start+horizon+self.b.probe_handling+self.b.probe_tail)
        self.cost['reserved_probe_horizon'] += horizon
        self.cost['handling'] += self.b.probe_handling
        self.cost['probe_tails'] += self.b.probe_tail
        return start, self.p.raw[begin:]

    def calibrate(self):
        if self.c.J != 0:
            raise ValueError('exact singleton calibration fixture requires J=0')
        for i in range(self.c.n):
            for op, duration in [('P',self.c.work_upper),('D',2*self.c.work_upper)]:
                t, reports = self._probe([Request(i,op)],duration)
                assert len(reports)==1
                self.local[i,op] = reports[0][0]-t
                self.cost['local_invocations'] += 1
        assert all(self.local[i,'D']==2*self.local[i,'P'] for i in range(self.c.n))
        assert len({self.local[i,'P'] for i in range(self.c.n)})==1

    def before(self, i, j):
        if self.c.J != 0:
            raise ValueError('first-arrival comparator certified only for J=0')
        Q = self.local[i,'P']
        t, raw = self._probe([Request(i,'D'),Request(j,'P')],3*Q)
        if len(raw)!=2 or raw[-1][0]-t!=3*Q or raw[0][0]-t not in (Q,2*Q):
            raise ValueError('diagnostic outside operational model')
        edge = (i,j) if raw[0][0]-t==2*Q else (j,i)
        self.edges.append(edge)
        closure(self.c.n,self.edges)  # reject inconsistent evidence, never certify vacuously
        self.comparisons.append(dict(pair=[i,j],start=t,raw=raw,edge=edge))
        self.cost['joint_invocations'] += 2
        return edge==(i,j)

    def learn_task_uniform(self, roles):
        """Learn only until all remaining incomparable pairs have one role.
        At most sum_{a<b} n_a*n_b actual probes; not an optimality claim.
        """
        while True:
            pred,succ=closure(self.c.n,self.edges)
            pair=next(((i,j) for i in range(self.c.n) for j in range(i+1,self.c.n)
                       if roles[i]!=roles[j] and j not in succ[i] and i not in succ[j]),None)
            if pair is None: break
            self.before(*pair)
        self.p.advance(self.p.now+self.b.compile)
        self.cost['compile']=self.b.compile
        return list(self.edges)

    def learn(self):
        def sort(xs):
            if len(xs)<2: return xs
            k=len(xs)//2
            a,c=sort(xs[:k]),sort(xs[k:])
            out=[]
            while a and c:
                out.append(a.pop(0) if self.before(a[0],c[0]) else c.pop(0))
            return out+a+c
        result=sort(list(range(self.c.n)))
        self.p.advance(self.p.now+self.b.compile)
        self.cost['compile'] = self.b.compile
        return result


def production(p, edges, roles, T0, b, deadline, requests=None, observed_now=None, local_work=None, caps=None):
    """Decision path never consults hidden priority, bits, IDs or service log."""
    c = caps if caps is not None else p.caps  # explicitly public supplied interface
    # Standalone controls use a supplied public work certificate; commissioned
    # runs explicitly pass the independently measured local certificate.
    if local_work is None:
        raise ValueError('a supplied or acquired sound work certificate is required')
    Q=local_work[0,'P']
    if local_work is not None and any(local_work[i,'P']!=Q for i in range(c.n)):
        return dict(status='REJECT_WORK_CERTIFICATE')
    if Q <= c.J:
        return dict(status='REJECT_RANK_GUARD')
    try: closure(c.n, edges)
    except ValueError: return dict(status='REJECT_CYCLE')
    if p.now>T0:
        return dict(status='REJECT_LATE')
    requests = requests if requests is not None else [Request(i,'P',True) for i in range(c.n)]
    if len(requests)!=c.n or sorted(r.module for r in requests)!=list(range(c.n)) or any(r.operation!='P' or not r.useful for r in requests):
        return dict(status='REJECT_REQUEST_MANIFEST')
    begin=len(p.raw)
    p.admit_batch(T0,requests)
    p.advance(T0+c.n*Q+c.J)
    raw=p.raw[begin:]
    if len(raw)!=c.n:
        return dict(status='REJECT_REPORT_HORIZON')
    now=p.now if observed_now is None else max(p.now,observed_now)
    if now+b.runtime+b.mission_tail>deadline:
        return dict(status='REJECT_REMAINING_BUDGET',now=now,deadline=deadline)
    cert=certify(c.n,edges,roles,[x[1] for x in raw])
    if not verify(c.n,edges,roles,[x[1] for x in raw],cert):
        return dict(status='REJECT_INVALID_CERTIFICATE')
    if cert['status']!='CERTIFIED':
        return dict(status='UNRESOLVED',certificate=cert,raw=raw)
    p.advance(now+b.runtime+b.mission_tail)
    return dict(status='COMMAND',vector=cert['parity'],raw=raw,finished=p.now,
                deadline=deadline,certificate=cert)


def truth_vector(p, roles):
    v={r:0 for r in roles}
    for j in p._truth_jobs:
        if j['useful']: v[roles[j['module']]] ^= j['bit']
    return v


def validate_local_contract(p):
    served=p._truth_service
    assert all(j['finish']-j['start']==j['demand'] for j in served)
    assert all(a['finish']<=b['start'] for a,b in zip(served,served[1:]))
    for i in range(p.n):
        ids=[j['index'] for j in served if j['module']==i]
        assert ids==sorted(ids)
    assert all(set(t)=={'time','bit'} for t in [dict(time=t,bit=b) for t,b in p.raw])


def known_work(n, Q=100):
    # Explicit supplied certificate for non-learning reference/control fixtures.
    return {(i,op):Q*(1+(op=='D')) for i in range(n) for op in ('P','D')}


def run_suite():
    b=Budget(); results=[]
    for n in (2,4,6,10):
        rng=random.Random(n)
        priorities=[list(range(n)),list(reversed(range(n)))]
        shuffled=list(range(n));rng.shuffle(shuffled);priorities.append(shuffled)
        for pi in priorities:
            for seed in range(5):
                p=Plant(pi,seed=seed)
                env=envelope(n,p.caps.work_upper,p.R,b)  # T0 fixed before observations, worst-case sorting bound
                learner=Learner(p,b,p.caps);learner.calibrate();order=learner.learn()
                assert order==pi  # validation only
                assert p.now<=env['T0']
                roles=list(range(n))
                out=production(p,learner.edges,roles,env['T0'],b,deadline=env['deadline'],local_work=learner.local)
                assert out['status']=='COMMAND' and out['vector']==truth_vector(p,roles)
                validate_local_contract(p)
                assert len(learner.comparisons)<=env['comparison_bound']
                results.append(dict(n=n,priority=pi,seed=seed,comparisons=len(learner.comparisons),
                    T0=env['T0'],finished=out['finished'],deadline=out['deadline'],
                    invocations=len(p._truth_jobs),cost=learner.cost,raw=out['raw'],command=out['vector']))
    controls={}
    # Completely arbitrary payload words, including non-iid adversarial realizations.
    words=0
    for n in (2,4,6,10):
        pi=list(reversed(range(n)));edges=list(zip(pi,pi[1:]))
        for bits in itertools.product((0,1),repeat=n):
            p=Plant(pi,payloads=bits)
            out=production(p,edges,list(range(n)),0,b,deadline=n*100+b.gamma,local_work=known_work(len(list(range(n)))))
            assert out['status']=='COMMAND' and out['vector']==truth_vector(p,list(range(n)))
            words+=1
    controls['arbitrary_payload_words_fullpriority']=words
    # Same local calibration observations in opposite latent-priority worlds.
    histories=[]
    for pi in ([0,1],[1,0]):
        p=Plant(pi,seed=11);l=Learner(p,b,p.caps);l.calibrate();histories.append((p.raw,l.local))
    assert histories[0]==histories[1]
    controls['local_calibration_priority_blind']=True
    # Same public upper caps permit genuinely unknown smaller intrinsic work.
    caps=PublicCaps(n=4,work_upper=100,R=400,J=0)
    env=envelope(caps.n,caps.work_upper,caps.R,b)
    p=Plant([2,0,3,1],Q=75,caps=caps,seed=91)
    l=Learner(p,b,caps);l.calibrate();l.learn()
    assert all(l.local[i,'P']==75 for i in range(4))
    out=production(p,l.edges,list(range(4)),env['T0'],b,deadline=env['deadline'],local_work=l.local,caps=caps)
    assert out['status']=='COMMAND' and out['vector']==truth_vector(p,list(range(4)))
    controls['unknown_work_below_public_cap']=dict(public_cap=100,learned_P=75,learned_D=150,T0=env['T0'],deadline=env['deadline'],raw=out['raw'])
    p=Plant([1,0],payloads=[0,1]);out=production(p,[],[0,1],0,b,deadline=220,local_work=known_work(len([0,1])))
    naive={0:out['raw'][0][1],1:out['raw'][1][1]}
    assert naive!=truth_vector(p,[0,1]) and out['status']=='UNRESOLVED'
    validate_local_contract(p)
    controls['local_only_wrong_naive_command']=dict(raw=out['raw'],naive=naive,truth=truth_vector(p,[0,1]),safe_status=out['status'])
    # No-learning exact certificate: accepts only constant words for distinct roles.
    accepted=0
    for bits in itertools.product((0,1),repeat=4):
        p=Plant([2,0,3,1],payloads=bits);out=production(p,[],list(range(4)),0,b,deadline=420,local_work=known_work(len(list(range(4)))))
        assert (out['status']=='COMMAND')==(len(set(bits))==1)
        accepted+=out['status']=='COMMAND'
    controls['nolearning_distinct_roles']=dict(accepted=accepted,total=16)
    # Partial evidence learned by safe probes; within-role priorities remain unknown.
    p=Plant([1,0,3,2],seed=44);env=envelope(4,p.caps.work_upper,p.R,b,comparison_bound=4);T0,deadline=env['T0'],env['deadline'];l=Learner(p,b,p.caps);l.calibrate()
    for i in (0,1):
        for j in (2,3): assert l.before(i,j)
    roles=['A','A','B','B'];p.advance(p.now+b.compile)
    out=production(p,l.edges,roles,T0,b,deadline=deadline,local_work=l.local)
    assert out['status']=='COMMAND' and out['vector']==truth_vector(p,roles)
    pred,succ=closure(4,l.edges)
    assert 1 not in succ[0] and 0 not in succ[1] and 3 not in succ[2] and 2 not in succ[3]
    controls['same_role_partial_identification']=dict(edges=l.edges,command=out['vector'])
    # Payload-specific partial certificate may pass despite cross-role ambiguity.
    p=Plant([1,0,2,3],payloads=[1,1,0,1])
    out=production(p,[(0,2),(1,2),(2,3)],list(range(4)),0,b,deadline=420,local_work=known_work(len(list(range(4)))))
    assert out['status']=='COMMAND'
    controls['payload_specific_partial_certificate']=True
    # Uniform task-relative acquisition: full priority is not its stopping goal.
    task_fixtures=[]
    for n in (2,4,6,10):
        for roles in ([0]*n,[i//2 for i in range(n)],list(range(n))):
            for pi in (list(range(n)),list(reversed(range(n)))):
                max_cross=sum(roles[i]!=roles[j] for i in range(n) for j in range(i+1,n))
                p=Plant(pi,seed=n+7);l=Learner(p,b,p.caps)
                env=envelope(n,p.caps.work_upper,p.R,b,comparison_bound=max_cross)
                l.calibrate();l.learn_task_uniform(roles)
                pred,succ=closure(n,l.edges)
                incomparables=[(i,j) for i in range(n) for j in range(i+1,n)
                              if j not in succ[i] and i not in succ[j]]
                assert all(roles[i]==roles[j] for i,j in incomparables)
                assert len(l.comparisons)<=max_cross and p.now<=env['T0']
                out=production(p,l.edges,roles,env['T0'],b,deadline=env['deadline'],local_work=l.local)
                assert out['status']=='COMMAND' and out['vector']==truth_vector(p,roles)
                if len(set(roles))==1: assert not l.comparisons
                task_fixtures.append(dict(n=n,roles=roles,priority=pi,probe_bound=max_cross,
                    probes=len(l.comparisons),remaining_incomparables=incomparables,T0=env['T0'],
                    command=out['vector']))
    controls['task_uniform_partial_learning']=task_fixtures
    # Actual six-world evidence/production coupling: exact joint-poset acceptance
    # is strictly stronger than marginal possible-rank perfect matching.
    chain_edges=[(0,3),(1,2)]; chain_roles=['A','B','A','B']; rank_bits=[0,0,1,1]
    extensions=[list(pi) for pi in itertools.permutations(range(4))
                if all(pi.index(i)<pi.index(j) for i,j in chain_edges)]
    assert len(extensions)==6
    worlds=[]
    for pi in extensions:
        # Test oracle conditions lawful arbitrary payload outcomes by world.
        # Neither learner nor production receives pi or this coupling rule.
        module_bits=[rank_bits[pi.index(i)] for i in range(4)]
        p=Plant(pi,payloads=[0]*12+module_bits)
        env=envelope(4,p.caps.work_upper,p.R,b,comparison_bound=2)
        T0,deadline=env['T0'],env['deadline']
        l=Learner(p,b,p.caps);l.calibrate()
        assert l.before(0,3) and l.before(1,2)
        p.advance(p.now+b.compile)
        out=production(p,l.edges,chain_roles,T0,b,deadline=deadline,local_work=l.local)
        assert out['status']=='COMMAND' and out['vector']=={'A':1,'B':1}
        assert out['vector']==truth_vector(p,chain_roles)
        worlds.append(dict(priority=pi,evidence=l.comparisons,raw=out['raw'],command=out['vector']))
    assert all(w['evidence']==worlds[0]['evidence'] and w['raw']==worlds[0]['raw'] for w in worlds)
    possible_ranks={i:{pi.index(i) for pi in extensions} for i in range(4)}
    impossible=[0,2,1,3]
    assert all(k in possible_ranks[i] for k,i in enumerate(impossible))
    assert impossible not in extensions
    impossible_vector={r:0 for r in chain_roles}
    for k,i in enumerate(impossible): impossible_vector[chain_roles[i]] ^= rank_bits[k]
    assert impossible_vector=={'A':0,'B':0}
    controls['physical_joint_poset_vs_marginal_rank_graph']=dict(
        worlds=worlds,roles=chain_roles,rank_bits=rank_bits,
        marginal_rank_sets={i:sorted(v) for i,v in possible_ranks.items()},
        impossible_matching=impossible,impossible_matching_vector=impossible_vector)
    # Serial baseline legal, correctly bound, but requires enlarged deadline/lease.
    p=Plant([3,1,0,2],payloads=[1,0,1,0]);v={}
    for i in range(4):
        k=len(p.raw);p.admit_batch(i*p.R,[Request(i,'P',True)]);p.advance(i*p.R+p.caps.work_upper)
        v[i]=p.raw[k][1]
    serial_finish=p.now+b.runtime+b.mission_tail
    assert v==truth_vector(p,list(range(4))) and serial_finish>4*p.caps.work_upper+b.gamma
    controls['serial_enlarged_deadline']=dict(finished=serial_finish,authorized_deadline=3*p.R+p.caps.work_upper+b.gamma,tight_deadline=4*p.caps.work_upper+b.gamma)
    # Callback order separation: passing jitter fixture and explicit reordering guard.
    p=Plant([1,0],J=3,payloads=[0,1],lags=[0,3]);out=production(p,[(1,0)],[0,1],0,b,deadline=220,local_work=known_work(len([0,1])))
    assert out['status']=='COMMAND' and out['vector']==truth_vector(p,[0,1])
    p=Plant([0,1],J=101,payloads=[0,1],lags=[101,0]);out=production(p,[(0,1)],[0,1],0,b,deadline=220,local_work=known_work(len([0,1])))
    assert out['status']=='REJECT_RANK_GUARD'
    p.admit_batch(0,[Request(0,'P'),Request(1,'P')]);p.advance(301)
    assert p.raw==[(200,1),(201,0)]
    controls['delayed_report_guard']=dict(status=out['status'],reordered_raw=p.raw)
    p=Plant([0,1]);p.advance(1);assert production(p,[],[0,1],0,b,deadline=220,local_work=known_work(len([0,1])))['status']=='REJECT_LATE'
    p=Plant([0,1]);assert production(p,[(0,1),(1,0)],[0,1],0,b,deadline=220,local_work=known_work(len([0,1])))['status']=='REJECT_CYCLE'
    p=Plant([0,1]);assert production(p,[],[0,1],0,b,deadline=220,requests=[Request(0,'P',True)]*3,local_work=known_work(len([0,1])))['status']=='REJECT_REQUEST_MANIFEST';assert not p._truth_jobs
    p=Plant([0,1]);assert production(p,[(0,1)],[0,1],0,b,deadline=220,observed_now=210,local_work=known_work(len([0,1])))['status']=='REJECT_REMAINING_BUDGET'
    controls['late_cycle_extra_jobs_actual_now_rejections']=True
    # Atomic batch, forbidden repeated same-tick commits, and persistent busy service.
    p=Plant([1,0],payloads=[0,1]);p.admit_batch(0,[Request(0,'P'),Request(1,'P')]);p.advance(200)
    assert [j['module'] for j in p._truth_service]==[1,0]
    q=Plant([1,0],payloads=[0,1]);q.admit_batch(0,[Request(0,'P')])
    try: q.admit_batch(0,[Request(1,'P')])
    except ValueError as e: assert 'one atomic batch commit' in str(e)
    else: raise AssertionError('same-tick sequential loophole')
    q=Plant([1,0]);q.admit_batch(0,[])
    try: q.admit_batch(0,[Request(1,'P')])
    except ValueError as e: assert 'one atomic batch commit' in str(e)
    else: raise AssertionError('empty-commit loophole')
    r=Plant([1,0],Q=100,R=100,payloads=[0,1]);r.admit_batch(0,[Request(0,'D')]);r.admit_batch(100,[Request(1,'P')]);r.advance(300)
    assert [(j['module'],j['start'],j['finish']) for j in r._truth_service]==[(0,0,200),(1,200,300)]
    # Completion-at-admission boundary: new high-priority head wins before dispatch.
    s=Plant([1,0],Q=100,R=100,payloads=[0,0,1]);s.admit_batch(0,[Request(0,'P'),Request(0,'P')]);s.admit_batch(100,[Request(1,'P')]);s.advance(300)
    assert [j['module'] for j in s._truth_service]==[0,1,0]
    controls['atomic_batch_boundary_and_no_busy_reset']=True
    return dict(summary=dict(end_to_end_fixtures=len(results),arbitrary_words=words,all_passed=True),controls=controls,fixtures=results)


if __name__=='__main__':
    result=run_suite()
    path=Path(__file__).with_name('reference_shared_pipeline_results.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(summary=result['summary'],controls=result['controls']),indent=2))
