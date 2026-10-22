"""Finite causal kernels, hidden-profile game compilation, and hierarchy certificates.

The imported distributed synthesis algorithm is not implemented here. --check
reproduces the compiler, hierarchy, transport, and physical-specialization evidence.
"""
from __future__ import annotations
import argparse
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import sys

if sys.flags.optimize:
    raise RuntimeError("Run without optimized Python; assertions are proof checks")
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "enforcement"))
from finite_model import BrakeConfig, BrakeState, Initial, Observation, Outcome, PeerBrakes, ProductPeerBrakes, Table, serial, service_free_rank, threshold_policy, verify


def frozen(value):
    """Canonical finite event labels; the caller declares which fields are consumed."""
    if hasattr(value, "__dataclass_fields__"):
        return frozen(serial(value))
    if isinstance(value, dict):
        return tuple((k, frozen(v)) for k, v in sorted(value.items()))
    if isinstance(value, (tuple, list)):
        return tuple(frozen(v) for v in value)
    if isinstance(value, (set, frozenset)):
        return tuple(sorted((frozen(v) for v in value), key=repr))
    return value


@dataclass(frozen=True)
class Base:
    fault: object
    world: object
    observation: Observation
    ages: tuple
    initial_inputs: tuple | None = None


@dataclass(frozen=True)
class Position:
    # base=-1 is the dummy root, base=-2 is an irreversibly losing completion.
    base: int
    incoming: tuple | None
    record: tuple


class Arena:
    def __init__(self, actors, profiles):
        self.actors, self.profiles = actors, tuple(profiles)
        self.bases, self.base_ids = [], {}
        self.positions = [Position(-1, None, ("bootstrap",))]
        self.position_ids = {self.positions[0]: 0}
        self.root_targets = set()
        self.transitions = {}  # (base, WHOLE profile) -> target position ids
        self.root = 0
        self.counts = {}
        self.unbounded_recurrence = {}

    def add_base(self, base):
        if base not in self.base_ids:
            self.base_ids[base] = len(self.bases)
            self.bases.append(base)
        return self.base_ids[base]

    def add_position(self, base, profile, record):
        vertex = Position(base, profile, record)
        if vertex not in self.position_ids:
            self.position_ids[vertex] = len(self.positions)
            self.positions.append(vertex)
        return self.position_ids[vertex]

    def failure(self, profile, reason, context):
        return self.add_position(-2, profile, ("failure", tuple(reason), frozen(context)))

    def beta(self, vertex, actor):
        p = self.positions[vertex]
        if p.base == -1:
            return ("root",)
        if p.base == -2:
            return ("terminal_failure",)
        b = self.bases[p.base]
        if b.initial_inputs is not None:
            return ("initial", b.initial_inputs[actor], b.observation.local[actor])
        return ("tick", b.observation.local[actor])

    def targets(self, vertex, profile):
        p = self.positions[vertex]
        if p.base == -1:
            return self.root_targets
        if p.base == -2:
            return frozenset((vertex,))
        return self.transitions[(p.base, tuple(profile))]

    def successors(self, vertex):
        return frozenset(t for a in self.profiles for t in self.targets(vertex, a))


def compile_kernel(kernel, commands, *, event_key=None, max_bases=250000):
    """Whole-arena compiler, independent of any selected controller.

    All nominal slots are regularly invoked. Faulty program recommendations are
    ignored by the source outcome callback, which retains actual faulty choices.
    An empty primitive branch must already be represented by the callback; this
    API cannot discover branches a model silently omitted. max_bases aborts rather
    than returning an unrealizability verdict.
    """
    if kernel.actors < 1 or len(commands) != kernel.actors or any(not domain for domain in commands):
        raise ValueError("Nonempty finite command domains required for every actor")
    profiles = tuple(itertools.product(*commands))
    arena = Arena(kernel.actors, profiles)
    event_key = event_key or (lambda outcome: frozen(outcome.event))
    faults = tuple(kernel.faults())
    if not faults:
        raise ValueError("Empty fault family is not a solved mission")
    arena.unbounded_recurrence = {f: tuple(name for name in kernel.recurrent_service(f)
        if name not in {n for n, _ in kernel.service(f)}) for f in faults}
    observations_cache = {}
    def observations(f, x):
        key = (f, x)
        if key not in observations_cache:
            obs = tuple(kernel.observations(f, x))
            if any(len(o.local) != kernel.actors or any(v is None for v in o.local) for o in obs):
                raise ValueError("This synchronous import does not expose missing calls as clock observations")
            observations_cache[key] = obs
        return observations_cache[key]
    initials = 0
    for f in faults:
        initial_family = tuple(kernel.initials(f))
        if not initial_family:
            raise ValueError("Every admitted fault requires actual initial scenarios")
        contracts = tuple(kernel.service(f))
        for init in initial_family:
            initials += 1
            if len(init.local_inputs) != kernel.actors:
                raise ValueError("Initial local inputs must be supplied per actor")
            ages = init.service_ages if init.service_ages is not None else (0,) * len(contracts)
            bad = tuple(kernel.initial_violations(f, init.state))
            if len(ages) != len(contracts) or any(d < 1 or not 0 <= a < d for a, (_, d) in zip(ages, contracts)):
                bad += ("invalid_initial_service_age",)
            obs = observations(f, init.state)
            if bad or not obs:
                arena.root_targets.add(arena.failure(None, bad or ("no_initial_observation",),
                    (f, init.state, tuple(init.local_inputs), tuple(ages))))
                continue
            for o in obs:
                b = arena.add_base(Base(f, init.state, o, tuple(ages), tuple(init.local_inputs)))
                arena.root_targets.add(arena.add_position(b, None, ("initial",)))
    outcomes_checked = masks_checked = 0
    cursor = 0
    while cursor < len(arena.bases):
        if len(arena.bases) > max_bases:
            raise RuntimeError("Operational arena limit reached; no synthesis verdict")
        b = arena.bases[cursor]
        contracts = tuple(kernel.service(b.fault))
        for profile in profiles:
            issued = tuple(profile[i] if kernel.compliant(b.fault, i) else None for i in range(kernel.actors))
            masks_checked += 1
            targets = set()
            outcomes = tuple(kernel.outcomes(b.fault, b.world, b.observation, issued))
            if not outcomes:
                targets.add(arena.failure(profile, ("no_effect_continuation",), (b.fault, b.world, b.observation)))
            for out in outcomes:
                outcomes_checked += 1
                ages = tuple(0 if name in out.delivered else age + 1 for age, (name, _) in zip(b.ages, contracts))
                bad = tuple(out.violations) + tuple("service_deadline:" + name for age, (name, d) in zip(ages, contracts) if age >= d)
                record = ("effect", tuple(sorted(out.delivered)), frozen(event_key(out)))
                if bad:
                    targets.add(arena.failure(profile, bad, (b.fault, out.state, record)))
                    continue
                following = observations(b.fault, out.state)
                if not following:
                    targets.add(arena.failure(profile, ("no_next_observation",), (b.fault, out.state, record)))
                for o in following:
                    nxt = arena.add_base(Base(b.fault, out.state, o, ages))
                    targets.add(arena.add_position(nxt, profile, record))
            if not targets:
                raise AssertionError("Totalization failed")
            arena.transitions[(cursor, profile)] = frozenset(targets)
        cursor += 1
    arena.root_targets = frozenset(arena.root_targets)
    assert arena.root_targets
    # Every productive edge carries the exact incoming WHOLE action profile.
    for (base, profile), targets in arena.transitions.items():
        for target in targets:
            assert arena.positions[target].incoming == profile
            if arena.positions[target].base >= 0:
                assert arena.bases[arena.positions[target].base].fault == arena.bases[base].fault
    arena.counts = {"faults": len(faults), "initial_scenarios": initials, "decision_bases": len(arena.bases),
                    "positions": len(arena.positions), "action_profiles": len(profiles),
                    "source_outcomes_enumerated": outcomes_checked, "profile_masks": masks_checked,
                    "distinct_profile_edges": sum(len(v) for v in arena.transitions.values()),
                    "failure_positions": sum(p.base == -2 for p in arena.positions)}
    return arena


def positional_hierarchy(arena):
    """Sufficient whole-arena certificate: fixed positional refinement order."""
    refinements = []
    for i in range(arena.actors):
        row = []
        for j in range(arena.actors):
            mapping, okay = {}, True
            for v in range(len(arena.positions)):
                a, b = arena.beta(v, i), arena.beta(v, j)
                if a in mapping and mapping[a] != b:
                    okay = False
                    break
                mapping[a] = b
            row.append(okay)
        refinements.append(row)
    if all(refinements[i][j] or refinements[j][i] for i in range(arena.actors) for j in range(arena.actors)):
        return {"hierarchical": True, "method": "whole-arena positional refinement",
                "refinement_matrix": refinements, "positions_checked": len(arena.positions)}
    return None


def hierarchy_test(arena):
    fast = positional_hierarchy(arena)
    if fast is not None:
        return fast
    successors = [arena.successors(v) for v in range(len(arena.positions))]
    explored = 0
    for i, j in itertools.combinations(range(arena.actors), 2):
        start = (arena.root, arena.root, arena.root, False, False)
        parents = {start: None}
        queue = deque((start,))
        while queue:
            node = queue.popleft()
            explored += 1
            v, left, right, di, dj = node
            if di and dj:
                path = []
                while node is not None:
                    path.append(node[:3]); node = parents[node]
                return {"hierarchical": False, "method": "full-arena triple witness",
                        "players": (i, j), "triple_states_checked": explored,
                        "witness": list(reversed(path))}
            for nv in successors[v]:
                ls = [l for l in successors[left] if arena.beta(l, i) == arena.beta(nv, i)]
                rs = [r for r in successors[right] if arena.beta(r, j) == arena.beta(nv, j)]
                for nl, nr in itertools.product(ls, rs):
                    nxt = (nv, nl, nr, di or arena.beta(nl, i) != arena.beta(nr, i),
                           dj or arena.beta(nl, j) != arena.beta(nr, j))
                    if nxt not in parents:
                        parents[nxt] = node; queue.append(nxt)
    return {"hierarchical": True, "method": "exhaustive full-arena triple search", "triple_states_checked": explored}


def check_witness(arena, result):
    if result["hierarchical"]:
        return
    i, j = result["players"]
    triples = result["witness"]
    assert triples[0] == (arena.root,) * 3
    for before, after in zip(triples, triples[1:]):
        assert all(v in arena.successors(u) for u, v in zip(before, after))
    actual, left, right = ([t[k] for t in triples[1:]] for k in range(3))
    view = lambda path, actor: tuple(arena.beta(v, actor) for v in path)
    assert view(actual, i) == view(left, i) and view(actual, j) == view(right, j)
    assert view(actual, j) != view(left, j) and view(actual, i) != view(right, i)


def verify_compiled_policy(arena, programs):
    """Replay a supplied finite policy; this is NOT the imported synthesis algorithm."""
    pending = deque()
    visited = set()
    for v in arena.root_targets:
        p = arena.positions[v]
        if p.base < 0:
            return {"winning": False, "reason": "initial_failure"}
        b = arena.bases[p.base]
        memory = tuple(t.start(j) for t, j in zip(programs, b.initial_inputs))
        pending.append((v, memory))
    edges = 0
    graph_edges = []
    while pending:
        node = pending.popleft()
        if node in visited: continue
        visited.add(node)
        v, memory = node
        b = arena.bases[arena.positions[v].base]
        reacted = tuple(t.react(m, o) for t, m, o in zip(programs, memory, b.observation.local))
        profile, next_memory = tuple(a for a, _ in reacted), tuple(m for _, m in reacted)
        # Hypothetical program memory updates even for faulty slots. No player reads f.
        for target in arena.targets(v, profile):
            edges += 1
            if arena.positions[target].base < 0:
                return {"winning": False, "reason": "admitted_failure", "positions": len(visited)}
            successor = (target, next_memory)
            graph_edges.append((node, successor, frozenset(arena.positions[target].record[1])))
            pending.append(successor)
    ranks = {}
    for f, names in arena.unbounded_recurrence.items():
        nodes = [n for n in visited if arena.bases[arena.positions[n[0]].base].fault == f]
        relevant = [e for e in graph_edges if arena.bases[arena.positions[e[0][0]].base].fault == f]
        for name in names:
            rank = service_free_rank(nodes, relevant, name)
            if rank is None:
                return {"winning": False, "reason": "service_free_cycle", "fault": repr(f), "service": name}
            ranks[repr((f,name))] = max(rank.values(), default=0)
    return {"winning": True, "positions_with_memory": len(visited), "checked_edges": edges,
            "unbounded_service_rank_maxima": ranks}


class PublicBrakes(PeerBrakes):
    def __init__(self):
        super().__init__(BrakeConfig(actors=2, fault_budget=1, heat_limit=4))
    def observations(self, fault, state):
        for label in ("low", "high"):
            if (label == "low" and state.x <= 3) or (label == "high" and state.x >= 2):
                yield Observation((label, label), state.x)


class PublicFleet(ProductPeerBrakes):
    """All planners receive the same target-label tuple; effects remain independent."""
    def __init__(self, devices=2, bad_motors=1):
        super().__init__(devices, bad_motors)
        self.local=PublicBrakes();self.actors=devices*self.local.actors
    def observations(self,fault,state):
        choices=[tuple(o.local[0] for o in self.local.observations(f,x)) for f,x in zip(fault.components,state)]
        for public in itertools.product(*choices):
            yield Observation((public,)*self.actors,tuple(x.x for x in state))
    def outcomes(self,fault,state,observation,issued):
        public=observation.local[0]
        if any(v!=public for v in observation.local):raise ValueError("Not the declared public interface")
        projected=Observation(tuple(public[j] for j in range(self.devices) for _ in range(self.local.actors)),observation.physical_sample)
        yield from super().outcomes(fault,state,projected,issued)


def fleet_check():
    fleet=PublicFleet();alphabet=tuple(itertools.product(("low","high"),repeat=fleet.devices))
    policies=tuple(Table(alphabet,("boot",),(0,),(tuple(int(o[i//2]=="high") for o in alphabet),),((0,)*len(alphabet),)) for i in range(fleet.actors))
    checked=0;minimum=None
    for fault in fleet.faults():
        for speeds,pending in (((4,4),(0,0)),((9,2),(1,1)),((2,9),(1,1))):
            state=tuple(BrakeState(x,4,(pending,),()) for x in speeds)
            for obs in fleet.observations(fault,state):
                assert all(o==obs.local[0] for o in obs.local)
                issued=tuple(p.react(0,obs.local[i])[0] if fleet.compliant(fault,i) else None for i,p in enumerate(policies))
                for out in fleet.outcomes(fault,state,obs,issued):
                    assert not out.violations and "aggregate" in out.delivered
                    amount=out.event["aggregate_delivery"]
                    assert amount>=fleet.devices-fleet.bad_motors
                    assert all(0<=x.x<=10 and 0<=x.heat<=4 for x in out.state)
                    minimum=amount if minimum is None else min(minimum,amount);checked+=1
    return {"devices":2,"faulty_motor_bound":1,"joint_fault_scenarios":len(tuple(fleet.faults())),
            "actual_outcomes_checked":checked,"minimum_actual_delivery_checked":minimum,
            "hierarchy_certificate":"all nominal local views are the same supplied public tuple",
            "general_floor":"J-p for J>=2 and p<J, by local closed-loop projection",
            "full_fleet_graph_enumerated":False}


class Tiny:
    actors = 2
    def __init__(self, kind="public", faults=None): self.kind, self._faults = kind, faults
    def faults(self): return self._faults if self._faults is not None else (0, 1)
    def compliant(self, f, i): return True
    def initials(self, f):
        inputs = itertools.product((0,1), repeat=2) if self.kind == "private_init" else ((0,0),)
        return tuple(Initial(b, tuple(j)) for b in (0,1) for j in inputs)
    def initial_violations(self, f, x): return ("initial_bad",) if self.kind == "bad_init" else ()
    def observations(self, f, x):
        if self.kind == "absent": return (Observation((None,0)),)
        if self.kind == "no_observation": return ()
        if self.kind == "mixed_fault": return (Observation((x,0) if f==0 else (0,x)),)
        if self.kind == "one_private": return (Observation(((0,x),0)),)
        return (Observation((0,0)),)
    def outcomes(self, f, x, observation, issued):
        if self.kind == "no_effect": return ()
        if self.kind == "late_bad":
            return (Outcome(x,frozenset(("s",)),(),{}), Outcome(x,frozenset(),("hostile_bad",),{}))
        if self.kind == "starve": return (Outcome(x,frozenset(),(),{}),)
        return tuple(Outcome(y,frozenset(("s",)),(),{}) for y in (0,1))
    def service(self, f): return (("s",1),)
    def recurrent_service(self, f): return ("s",)


def compiler_regressions():
    results = {}
    for kind in ("public", "private_init", "mixed_fault", "one_private"):
        arena = compile_kernel(Tiny(kind), ((0,1),(0,1)))
        result = hierarchy_test(arena); check_witness(arena,result)
        assert result["hierarchical"] == (kind in ("public","one_private"))
        results[kind] = {**arena.counts, "hierarchy": result}
    # Each known-fault slice is hierarchical, while their unknown-fault union is not.
    for f in (0,1):
        assert hierarchy_test(compile_kernel(Tiny("mixed_fault",(f,)), ((0,1),(0,1))))["hierarchical"]
    for kind in ("bad_init","no_observation","no_effect","late_bad","starve"):
        arena = compile_kernel(Tiny(kind), ((0,1),(0,1)))
        assert any(p.base == -2 for p in arena.positions)
        tables=(Table((0,), (0,), (0,), ((0,),), ((0,),)),)*2
        assert not verify_compiled_policy(arena,tables)["winning"]
        results[kind] = arena.counts
    try:
        compile_kernel(Tiny("absent"), ((0,1),(0,1)))
        raise AssertionError("Missing invocation became an observable synchronous tick")
    except ValueError:
        pass
    labels={(0,1),(1,0)}; wanted=(0,0)
    assert all(any(a[i]==wanted[i] for a in labels) for i in range(2)) and wanted not in labels
    results["quantifier_regression"]={"separate_profile_witnesses_exist":True,"whole_profile_edge_exists":False,
                                      "compiler_keeps_incoming_whole_profile":True}
    results["missing_invocation_rejected"]=True
    class UnboundedStarvation(Tiny):
        def service(self,f):return ()
        def outcomes(self,f,x,o,a):return (Outcome(x,frozenset(),(),{}),)
    arena=compile_kernel(UnboundedStarvation(),((0,1),(0,1)))
    tables=(Table((0,), (0,), (0,), ((0,),), ((0,),)),)*2
    assert verify_compiled_policy(arena,tables)["reason"]=="service_free_cycle"
    results["unbounded_starvation_rejected"]=True
    class Masked(Tiny):
        def compliant(self,f,i):return i!=f
        def outcomes(self,f,x,o,a):
            assert a[f] is None
            return tuple(Outcome(y,frozenset(("s",)),(),{"actual_faulty_command":y}) for y in (0,1))
    arena=compile_kernel(Masked(),((0,1),(0,1)))
    compared=0
    for b,base in enumerate(arena.bases):
        first={}
        for profile in arena.profiles:
            unaffected=tuple(a for i,a in enumerate(profile) if i!=base.fault)
            image={(arena.positions[v].base,arena.positions[v].record) for v in arena.transitions[(b,profile)]}
            if unaffected in first:assert first[unaffected]==image
            first[unaffected]=image;compared+=1
    results["ignored_faulty_recommendation_profiles_checked"]=compared
    class InitializerAware(Tiny):
        def initials(self,f):return tuple(Initial(x,(x,0)) for x in (0,1))
        def outcomes(self,f,x,o,a):return (Outcome(x,frozenset(("s",)),() if a[0]==x else ("initializer_needed",),{}),)
    aware=InitializerAware();arena=compile_kernel(aware,((0,1),(0,1)))
    programs=(Table((0,),(0,1),(0,1),((0,),(1,)),((0,),(1,))),tables[1])
    assert verify(aware,programs)["winning"] and verify_compiled_policy(arena,programs)["winning"]
    assert hierarchy_test(arena)["hierarchical"]
    results["private_initializer_policy_transport"]={"nonconstant_local_initial_map":True,"source_and_compiled_winning":True}
    class Crossing(Tiny):
        def faults(self):return (0,)
        def initials(self,f):return tuple(Initial((0,x,0),(0,0)) for x in (0,1))
        def observations(self,f,state):
            stage,x,y=state
            local=(("private",x),("blank",)) if stage==0 else (
                (("reveal",x),("reveal",x)) if stage==1 else (
                (("after",),("second",y)) if stage==2 else (("end",),("end",))))
            return (Observation(local),)
        def outcomes(self,f,state,o,a):
            stage,x,y=state
            successors=((1,x,0),) if stage==0 else (
                ((2,x,0),(2,x,1)) if stage==1 else ((3,x,y),))
            return tuple(Outcome(s,frozenset(("s",)),(),{}) for s in successors)
    crossing=compile_kernel(Crossing(),((0,),(0,)))
    assert positional_hierarchy(crossing) is None
    cross_result=hierarchy_test(crossing)
    assert cross_result["hierarchical"] and cross_result["method"]=="exhaustive full-arena triple search"
    results["dynamic_order_change"]=cross_result
    plain=compile_kernel(Tiny(),((0,1),(0,1)))
    class EchoView:
        actors=plain.actors;positions=plain.positions;root=plain.root
        def successors(self,v):return plain.successors(v)
        def beta(self,v,i):
            incoming=plain.positions[v].incoming
            return (plain.beta(v,i),("own",incoming[i]) if incoming is not None else ("initial",))
    echo=EchoView();echo_result=hierarchy_test(echo);check_witness(echo,echo_result)
    assert not echo_result["hierarchical"]
    results["own_action_observations_change_full_arena_information"]=echo_result
    return results


def frontend_check():
    count=0
    for x,bad in itertools.product(range(13),range(-1,3)):
        images=set()
        for bits in itertools.product((0,1),repeat=3):
            if any(i!=bad and ((v==0 and x>=4) or (v==1 and x<=1)) for i,v in enumerate(bits)):
                continue
            label="high" if sum(bits)>=2 else "low"
            assert (label=="low" and x<=3) or (label=="high" and x>=2)
            images.add(label);count+=1
        expected={v for v in ("low","high") if (v=="low" and x<=3) or (v=="high" and x>=2)}
        assert images==expected
    return {"checked_vectors":count,"fault_masks":4,"public_signal":"same derived label at both planners",
            "raw_report_strategy_reflection":False}


def memory_rewrite_check():
    checked=0
    # The source update explicitly reads its actual own action; the rewritten one
    # substitutes the locally determined action, including nonconstant initialization.
    for initial in (0,1):
        for observations in itertools.product((0,1),repeat=8):
            source=compiled=initial
            for observation in observations:
                actual=(source+observation)%2
                predicted=(compiled+observation)%2
                assert actual==predicted
                source=(source+observation+actual+1)%3
                compiled=(compiled+observation+predicted+1)%3
                assert source==compiled
            checked+=1
    return {"streams_checked":checked,"claim":"policy-relative deterministic own-action reconstruction"}


def reproduce():
    regressions=compiler_regressions()
    kernel=PublicBrakes()
    arena=compile_kernel(kernel,((0,1),(0,1)),event_key=lambda out:("actual_delivery",out.event["actual_delivery"]))
    hierarchy=hierarchy_test(arena)
    assert hierarchy["hierarchical"] and all(all(row) for row in hierarchy["refinement_matrix"])
    policies=threshold_policy(actors=2)
    source=verify(kernel,policies,full=True)
    compiled=verify_compiled_policy(arena,policies)
    assert source["winning"] and compiled["winning"]
    c=Fraction(1,2);T=Fraction(6);b=Fraction(1);V=Fraction(10);q=Fraction(3);eps=Fraction(1)
    growth=(1-c)**2*(q+eps)+(T/c)*(1-(1-c)**2)
    assert growth==10 and b*(2-1)>=T-c*V
    assert Fraction(4)>=c+2*b and Fraction(1,10)*b*2*V <= (1-Fraction(1,2))*4
    fingerprint=hashlib.sha256()
    for key,targets in sorted(arena.transitions.items(),key=lambda z:repr(z[0])):
        fingerprint.update(repr((key,tuple(sorted(targets)))).encode())
    return {"scope":"finite regular-invocation causal kernels; full unknown-fault arena; checked synthesis import",
            "imported_synthesis_algorithm_executed":False,
            "compiler_regressions":regressions,"frontend":frontend_check(),"own_action_rewrite":memory_rewrite_check(),
            "fleet":fleet_check(),
            "public_brakes":{"compiler":arena.counts,"hierarchy":hierarchy,"source_policy_check":source,
                "compiled_policy_check":compiled,"arena_edge_sha256":fingerprint.hexdigest(),
                "exact_parameter_margins":{"normal":"3/2","surviving_force":"0","delay_envelope":"10","thermal":"0","conduct_lower":"2"}},
            "aggregate_service":{"family":"J>=2, p<J faultable motor/output chains; same public tuple at every planner",
                "actual_floor":"J-p per physical tick","heat":"4J for separate stores; shared heat needs summed load proof",
                "full_fleet_graph_enumerated":False}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check",action="store_true");group.add_argument("--write",action="store_true")
    args=parser.parse_args();result=reproduce()
    names=("hierarchy_model.py","Hierarchy.lean","HIERARCHY.md","HIERARCHY-SOURCES.md","../enforcement/finite_model.py")
    result["source_sha256_lf"]={name:hashlib.sha256((HERE/name).read_bytes().replace(b"\r\n",b"\n")).hexdigest() for name in names}
    encoded=json.dumps(result,indent=2,sort_keys=True)+"\n";path=HERE/"hierarchy_results.json"
    if args.write:path.write_text(encoded,encoding="utf-8")
    elif path.read_text(encoding="utf-8").replace("\r\n","\n")!=encoded:raise RuntimeError("Evidence changed; inspect before regeneration")
    print(json.dumps({"verified":True,"compiler":result["public_brakes"]["compiler"],"synthesis_algorithm_executed":False}))


if __name__=="__main__":main()
