"""Local make-before-break enactment with fallible suppliers and authorities.

Run with Python 3.12 and -B. --write regenerates JSON; --check compares exactly.
The Kernel API is the existing enforcement finite interface. No third-party package.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import sys
from dataclasses import dataclass, replace
from pathlib import Path

if sys.flags.optimize:
    raise RuntimeError("Assertions are required")
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "enforcement"))
from finite_model import Initial, Observation, Outcome, Table, serial, verify

SCOPE = ("peer-brake-substitution", 0, 1, 2, 3)

def speed(x, u, e):
    return max(0, (5*x + 10*u - 10*e) // 10)

def heat(h, e, x):
    return (5*h + e*x) // 10

def high(x):
    return int(x >= 2)

@dataclass(frozen=True)
class Fault:
    motor_bad: bool
    chain: int = -1
    planner_bad: bool = False
    actuator_bad: bool = False
    installer_bad: bool = False
    authority: int = -1

@dataclass(frozen=True)
class State:
    x: int
    heat: int
    pending: tuple[int, int, int, int]
    last_sample: int
    spare_stage: int  # ordinary control path: 0 unavailable, 1 warming, 2 warm
    ready: bool      # artifact issued by the spare's planner, not a clean bit
    votes: int      # distinct scoped signatures received by old planner 2
    retired: bool  # old path's release latch; faulty effect can ignore it
    evidence_scope: tuple = SCOPE

    @property
    def recognized(self):
        return int(self.votes.bit_count() >= 2)

@dataclass(frozen=True)
class Signature:
    signer: int
    scope: tuple
    purpose: str
    authentic: bool = True


def public_verify(signatures, scope=SCOPE):
    """Ideal authenticated tokens, then scope/type checks, then deduplication.

    This proves neither physical readiness nor computational signature security.
    Honest issuance and the fault-indexed READY argument provide those consumers.
    """
    ids = {s.signer for s in signatures
           if s.authentic and s.scope == scope and s.purpose == "approve"
           and s.signer in (0, 1, 2)}
    return len(ids) >= 2


def valid_ready(message):
    return (message.authentic and message.signer == 3
            and message.scope == SCOPE and message.purpose == "ready")


def next_metadata(fault, state, commands, vote, selected):
    if fault.installer_bad:
        stages = range(3)
    elif state.spare_stage == 0:
        stages = (0, 1) if commands[3] & 2 else (0,)
    elif state.spare_stage == 1:
        stages = (2,)
    else:
        stages = (2,)
    votes = state.votes | ((1 << selected) if selected >= 0 and vote else 0)
    for stage in stages:
        yield (stage, state.ready or bool(commands[3] & 4), votes,
               state.retired or bool(commands[2] & 2))


def physical_interface(fault, state):
    return ((not state.ready or fault.chain == 3 or state.spare_stage == 2)
            and (state.votes.bit_count() < 2 or state.ready)
            and (not state.retired or fault.chain == 2 or state.recognized))


def metadata_invariant(fault, state):
    return (physical_interface(fault, state)
            and all(not (state.votes & (1 << j)) or j == fault.authority or state.ready
                    for j in range(3)))


def all_faults():
    chains = [(-1, False, False, False)]
    for chain in range(4):
        for role in range(1, 8 if chain == 3 else 4):
            chains.append((chain, bool(role & 1), bool(role & 2), bool(role & 4)))
    for motor_bad in (False, True):
        for chain, planner, actuator, installer in chains:
            for authority in (-1, 0, 1, 2):
                yield Fault(motor_bad, chain, planner, actuator, installer, authority)


def policies(wrong_order=False):
    answer = []
    for i in range(4):
        labels, outputs = [], []
        for bit in (0, 1):
            if i < 2:
                labels.append(f"h{bit}")
                outputs.append(bit)
            elif i == 2:
                for certificate in (0, 1):
                    labels.append(f"h{bit}|c{certificate}")
                    outputs.append(bit + 2*int(wrong_order or certificate))
            else:
                for stage in range(3):
                    labels.append(f"h{bit}|s{stage}")
                    outputs.append(bit + 2*int(stage == 0) + 4*int(stage == 2))
        answer.append(Table(tuple(labels), ("boot",), (0,), (tuple(outputs),),
                            ((0,)*len(labels),)))
    for _ in range(3):
        answer.append(Table(("missing", "ready"), ("boot",), (0,), ((0, 1),), ((0, 0),)))
    return tuple(answer)


class Enactment:
    actors = 7
    def __init__(self, faults=None, *, wrong_order=False):
        self._faults = tuple(all_faults()) if faults is None else tuple(faults)
        self.wrong_order = wrong_order

    def faults(self):
        return iter(self._faults)

    def compliant(self, fault, actor):
        if actor < 4:
            return not (fault.planner_bad and actor == fault.chain)
        return actor - 4 != fault.authority

    def initials(self, fault):
        for x in ((0, 1) if fault.motor_bad else (1,)):
            # All heat values are admitted and covered by the stream theorem.
            # Finite graph starts at the maximal resource load; other initial
            # heat values are covered by the monotone heat projection below.
            yield Initial(State(x, 8, (0, 0, 0, 0), x, 0, False, 0, False),
                          ("boot",)*7)

    def initial_violations(self, fault, state):
        return self.world_violations(fault, state)

    def world_violations(self, fault, state):
        bad = []
        if not 0 <= state.x <= 10:
            bad.append("world_speed")
        if not 0 <= state.heat <= 8:
            bad.append("world_heat")
        if not fault.motor_bad and state.x < 1:
            bad.append("normal_actual_service")
        return tuple(bad)

    def observations(self, fault, state):
        bit = high(state.x)
        stages = range(3) if fault.installer_bad else (state.spare_stage,)
        # A scheduled authorization request is delivered to at most one office
        # per physical interval. Absence is legal; physical service still runs.
        for stage in stages:
            for selected in (-1, 0, 1, 2):
                local = [f"h{bit}", f"h{bit}", f"h{bit}|c{state.recognized}",
                         f"h{bit}|s{stage}"]
                local.extend(("ready" if state.ready else "missing")
                             if j == selected else None for j in range(3))
                yield Observation(tuple(local), state.x)

    def outcomes(self, fault, state, observation, issued):
        options = []
        for i in range(4):
            if self.compliant(fault, i):
                if issued[i] is None:
                    yield Outcome(state, frozenset(), ("missing_brake_invocation",), {})
                    return
                options.append((issued[i],))
            else:
                options.append(range(2 if i < 2 else 4 if i == 2 else 8))
        selected = next((j for j in range(3) if observation.local[j+4] is not None), -1)
        auth_options = ((0, 1) if selected == fault.authority and selected >= 0
                        else (issued[selected+4],) if selected >= 0 else (0,))
        for commands in itertools.product(*options):
            conduct = []
            for i in range(4):
                if self.compliant(fault, i) and commands[i] & 1 and state.x < 2:
                    conduct.append("issued_on_without_current_justification")
            if self.compliant(fault, 2) and commands[2] & 2 and not state.recognized:
                # The wrong-order comparison deliberately changes this rule to
                # permission for immediate release, so its failure is physical.
                if not self.wrong_order:
                    conduct.append("retirement_without_authority")
            if self.compliant(fault, 3) and commands[3] & 4 and not observation.local[3].endswith("s2"):
                conduct.append("ready_without_local_install_ack")
            q = tuple(c & 1 for c in commands)
            engagements = []
            for i in range(4):
                if fault.actuator_bad and i == fault.chain:
                    engagements.append((0, 1))
                elif i == 2 and state.retired:
                    engagements.append((0,))
                elif i == 3 and state.spare_stage != 2:
                    engagements.append((0,))
                else:
                    engagements.append((state.pending[i],))
            motors = range(8) if fault.motor_bad else (5,)
            for es in itertools.product(*engagements):
                total = sum(es)
                for u in motors:
                    nx = speed(state.x, u, total)
                    nh = heat(state.heat, total, state.x)
                    # The carrier permits unsafe values. No transition is clipped
                    # to the mission; an attack may reach x=11 or heat=9.
                    assert 0 <= nx <= 14 and 0 <= nh <= 12
                    for vote in auth_options:
                        for stage, ready, votes, retired in next_metadata(fault,state,commands,vote,selected):
                            ns = State(nx, nh, q, state.x, stage, ready, votes, retired, state.evidence_scope)
                            bad = tuple(conduct) + self.world_violations(fault, ns)
                            # Faulty output may withhold everything; the minimal
                            # delivered quantity suffices for every lower-bound query.
                            quantity = 0 if fault.motor_bad else nx
                            delivered = frozenset(("normal",)) if quantity > 0 else frozenset()
                            event = {"commands": commands, "engagements": es, "motor": u,
                                     "selected_authority": selected, "vote": vote,
                                     "actual_delivered": quantity,
                                     "recognized": ns.recognized, "spare_stage": stage,
                                     "retired": ns.retired}
                            yield Outcome(ns, delivered, bad, event)

    def service(self, fault):
        return () if fault.motor_bad else (("normal", 1),)

    def recurrent_service(self, fault):
        return ()


def react(kernel, fault, state, observation, local_policies):
    return tuple(local_policies[i].react(0, observation.local[i])[0]
                 if kernel.compliant(fault, i) else None for i in range(kernel.actors))


def check_public_evidence():
    count = 0
    for bad in (-1, 0, 1, 2):
        for ready in (False, True):
            for mask in range(8):
                # Constructible issued signatures: an honest office must have
                # received READY; a corrupt office can sign without that event.
                if any(mask & (1 << j) and j != bad and not ready for j in range(3)):
                    continue
                tokens = [Signature(j, SCOPE, "approve") for j in range(3) if mask & (1 << j)]
                accepted = public_verify(tokens)
                assert not accepted or ready
                count += 1
    a, b = Signature(0, SCOPE, "approve"), Signature(1, SCOPE, "approve")
    assert public_verify([a, b])
    assert not public_verify([a, a])
    assert not public_verify([replace(a, authentic=False), b])
    assert not public_verify([replace(a, scope=("old",)), b])
    assert not public_verify([replace(a, purpose="ready"), b])
    assert public_verify([replace(a, scope=("old",)), a, b])
    assert valid_ready(Signature(3, SCOPE, "ready"))
    assert not valid_ready(Signature(3, ("old",), "ready"))
    return {"constructible_authority_profiles": count, "valid_available_artifact": serial([a,b]),
            "rejections": ["duplicate", "forgery", "stale_scope", "wrong_purpose"],
            "invalid_before_valid_same_identity": "accepted"}


def check_sources():
    total = 0
    for x in range(15):
        truth = high(x)
        for reports in itertools.product((0,1), repeat=3):
            if sum(r == truth for r in reports) >= 2:
                value = int(sum(reports) >= 2)
                assert value == truth
                assert not value or x >= 2
                total += 1
    return {"source_vectors": total, "intact_error": 0, "faultable_paths_per_frontend": 1,
            "frontend_paths": 3}


def check_survival_lemma():
    count = 0
    for bs in itertools.product((0,1), repeat=4):
        if sum(bs) > 1:
            continue
        for retired, ready, warm in itertools.product((0,1), repeat=3):
            if retired and not (bs[2] or ready):
                continue
            if ready and not (bs[3] or warm):
                continue
            for es in itertools.product((0,1), repeat=4):
                active = (1, 1, 1-retired, warm)
                if any(not bs[i] and active[i] and not es[i] for i in range(4)):
                    continue
                assert sum(es) >= 2
                count += 1
    return {"high_sample_effect_profiles": count}


def check_physics():
    count = 0
    for x in range(11):
        for u in range(8):
            for e in range(5):
                if e >= 2 or x <= 7:
                    assert 0 <= speed(x,u,e) <= 10
                if x <= 1:
                    assert speed(x,u,e) <= 7
                if x >= 1:
                    assert speed(x,5,e) >= 1
                for h in range(9):
                    assert 0 <= heat(h,e,x) <= 8
                    if h < 8:
                        assert heat(h,e,x) <= heat(h+1,e,x)
                    count += 1
    return {"physical_parameter_tuples": count,
            "heat_initial_downward_simulation": "same speed/commands, smaller heat stays smaller",
            "normal_worst_case": speed(1,5,4), "shared_heat_boundary": heat(8,4,10)}


def protocol_witnesses():
    ps = policies()
    f = Fault(True, 0, False, True, False, -1)
    k = Enactment([f])
    s = next(k.initials(f)).state
    records = []
    # A constructible successful sequence: install, warm, publish, two local
    # approval requests, observe certificate, retire. Other actions still operate.
    for selected in (-1,-1,-1,0,1,-1,-1):
        obs = next(o for o in k.observations(f,s)
                   if next((j for j in range(3) if o.local[j+4] is not None),-1) == selected)
        outs = k.outcomes(f,s,obs,react(k,f,s,obs,ps))
        # Choose maximal drive, broken old brake OFF, successful installation.
        outcome = next(o for o in outs if o.event["motor"] == 7
                       and o.event["engagements"][0] == 0
                       and o.state.spare_stage == (1 if s.spare_stage == 0 else 2))
        assert not outcome.violations
        records.append({"before":serial(s),"event":serial(outcome.event),"after":serial(outcome.state)})
        s=outcome.state
    assert s.retired and s.spare_stage == 2 and s.recognized == 1
    # A fallible installer can acknowledge a nonexistent spare. Since this is the
    # one bad chain, the two retained old chains suffice after authorized retirement.
    ff = Fault(False,3,False,False,True,0)
    kk = Enactment([ff])
    ss = next(kk.initials(ff)).state
    false_ready = []
    for selected in (-1,0,1,-1,-1):
        obs = next(o for o in kk.observations(ff,ss)
                   if o.local[3].endswith("s2") and next((j for j in range(3) if o.local[j+4] is not None),-1)==selected)
        outcome = next(o for o in kk.outcomes(ff,ss,obs,react(kk,ff,ss,obs,ps))
                       if o.state.spare_stage == 0 and (selected != 0 or o.event["vote"] == 1))
        assert not outcome.violations and outcome.event["actual_delivered"] >= 1
        false_ready.append({"before":serial(ss),"event":serial(outcome.event),"after":serial(outcome.state)})
        ss=outcome.state
    assert ss.retired and ss.recognized == 1 and ss.spare_stage == 0
    return {"successful_substitution": records, "false_ready_safe_failed_install": false_ready}


def holding_cycle():
    f=Fault(False,0,False,True,False,0)
    k=Enactment([f])
    ps=policies()
    s=next(k.initials(f)).state
    seen={}
    records=[]
    while s not in seen:
        seen[s]=len(records)
        obs=next(k.observations(f,s))  # idle authority slot, truthful stage report
        o=next(o for o in k.outcomes(f,s,obs,react(k,f,s,obs,ps))
               if o.state.spare_stage==0 and o.event["engagements"][0]==0)
        assert not o.violations and o.event["actual_delivered"]>=1
        records.append({"before":serial(s),"event":serial(o.event),"after":serial(o.state)})
        s=o.state
        assert len(records)<100
    assert not s.recognized and not s.retired and s.spare_stage==0
    return {"prefix_length":seen[s],"cycle_length":len(records)-seen[s],"trace":records}


def wrong_order_witness():
    # Immediate retirement is explicitly permitted in this comparison, removing
    # the authority violation as a possible explanation of the physical failure.
    f = Fault(True,0,False,True,False,-1)
    k = Enactment([f],wrong_order=True)
    ps = policies(wrong_order=True)
    s = State(1,8,(0,0,0,0),1,0,False,0,True)
    records=[]
    for _ in range(3):
        obs=next(k.observations(f,s))
        o=next(o for o in k.outcomes(f,s,obs,react(k,f,s,obs,ps))
               if o.event["motor"]==7 and o.event["engagements"][0]==0 and o.state.spare_stage==0)
        records.append({"before":serial(s),"event":serial(o.event),"after":serial(o.state),
                        "violations":o.violations})
        s=o.state
    assert [r["after"]["x"] for r in records] == [7,10,11]
    assert records[-1]["violations"] == ("world_speed",)
    return records


def check_metadata():
    states = edges = 0
    # Motor faults do not enter these transitions or local administrative guards.
    fs = [f for f in all_faults() if not f.motor_bad]
    ps = policies()
    for f in fs:
        k=Enactment([f])
        for stage,ready,votes,retired in itertools.product(range(3),(False,True),range(8),(False,True)):
            state=State(2,0,(1,1,1,1),2,stage,ready,votes,retired)
            if not metadata_invariant(f,state):
                continue
            states += 1
            for obs in k.observations(f,state):
                issued=react(k,f,state,obs,ps)
                selected=next((j for j in range(3) if obs.local[j+4] is not None),-1)
                old_options=(0,2) if f.planner_bad and f.chain==2 else (issued[2] & 2,)
                new_options=(0,2,4,6) if f.planner_bad and f.chain==3 else (issued[3] & 6,)
                va=(0,1) if selected==f.authority and selected>=0 else (issued[selected+4],) if selected>=0 else (0,)
                seen=False
                for old,new,vote in itertools.product(old_options,new_options,va):
                    commands=(1,1,1+old,1+new)
                    for ns_stage,ns_ready,ns_votes,ns_retired in next_metadata(f,state,commands,vote,selected):
                        ns=replace(state,spare_stage=ns_stage,ready=ns_ready,votes=ns_votes,retired=ns_retired)
                        assert metadata_invariant(f,ns)
                        assert ns.evidence_scope == state.evidence_scope == SCOPE
                        assert ns.votes | state.votes == ns.votes
                        if f.chain!=3 and state.spare_stage==2:
                            assert ns.spare_stage==2
                        edges+=1
                        seen=True
                assert seen
    return {"fault_role_projections":len(fs),"invariant_states":states,"all_protocol_edges":edges,
            "factorization":"administrative auxiliaries do not depend on drive bit, heat or motor fault"}


def check_effect_adapter():
    count=0
    fs=[f for f in all_faults() if not f.motor_bad and f.authority==-1]
    for f in fs:
        for stage,ready,votes,retired in itertools.product(range(3),(False,True),range(8),(False,True)):
            state=State(2,0,(1,1,1,1),2,stage,ready,votes,retired)
            if not physical_interface(f,state):
                continue
            for previous_bit in (0,1):
                queues=[(0,1) if f.planner_bad and f.chain==i else (previous_bit,) for i in range(4)]
                for pending in itertools.product(*queues):
                    choices=[]
                    for i in range(4):
                        if f.actuator_bad and f.chain==i:
                            choices.append((0,1))
                        elif i==2 and retired:
                            choices.append((0,))
                        elif i==3 and stage!=2:
                            choices.append((0,))
                        else:
                            choices.append((pending[i],))
                    for es in itertools.product(*choices):
                        assert 0 <= sum(es) <= 4
                        assert not previous_bit or sum(es)>=2
                        count+=1
    # Distinct authority identities affect only the proved ready/certificate
    # invariant; the physical adapter consumes that invariant, not their names.
    return {"all_pending_effect_profiles":count,"physical_chain_role_projections":len(fs)}


def check_delayed_certificate():
    count=0
    for old,old_u,old_e in itertools.product(range(11),range(8),range(5)):
        current=speed(old,old_u,old_e)
        if current>10:
            continue
        for u,e in itertools.product(range(8),range(5)):
            if old>=2 and e<2:
                continue
            assert speed(current,u,e)<=10
            count+=1
    return {"all_delayed_physical_steps":count}


def check_local_tables():
    count=0
    for i,table in enumerate(policies()):
        for label in table.observations:
            command,_=table.react(0,label)
            if i<4:
                bit=int(label[1])
                assert command & 1 == bit
                if i==2:
                    assert bool(command & 2)==label.endswith("c1")
                if i==3:
                    assert bool(command & 2)==label.endswith("s0")
                    assert bool(command & 4)==label.endswith("s2")
            else:
                assert command==int(label=="ready")
            count+=1
    return {"all_local_table_entries":count,"memory_bound":1}


def check_parameter_family():
    examples=[]
    for m,f,k,q,T,U,V,H in ((3,1,1,2,7,5,10,8),(5,2,2,2,9,8,14,20)):
        maximum=m+k
        survivors=m-f
        low=(q-1+2*T)//2
        assert m>=k>=1 and q>=2 and 0<=f<m and maximum+1<=U<=T
        assert 2*T-2*survivors<=V
        assert (low+2*T)//2<=V
        assert maximum*V<=5*H
        examples.append(dict(old_slots=m,joint_fault_budget=f,replacement_pairs=k,
                             threshold=q,hostile_max=T,normal_supply=U,safety_limit=V,
                             heat_limit=H,minimum_survivors=survivors))
    return examples


def reproduce(full=False):
    result={"scope":"static joint faults; one preauthorized replacement; exact intact binary sources",
            "source_adapter":check_sources(),"local_tables":check_local_tables(),
            "parameter_family":check_parameter_family(),"public_evidence":check_public_evidence(),
            "surviving_effect":check_survival_lemma(),"physics":check_physics(),
            "protocol_closure":check_metadata(),"pending_effect_adapter":check_effect_adapter(),
            "delayed_physical_closure":check_delayed_certificate(),
            "witnesses":protocol_witnesses(),"holding_cycle":holding_cycle(),"wrong_order":wrong_order_witness()}
    result["finite_certificate"]={"method":"exact factorized inductive certificate, not reachable-graph sampling",
        "full_identity_fault_classes":len(tuple(all_faults())),
        "factor_assembly":"same joint fault; protocol closure -> surviving delayed effects -> physical safety and service; source frontend preserves correct-planner conduct"}
    if full:
        result["full_graph"]=verify(Enactment(),policies(),recurrent=False,full=False)
        assert result["full_graph"]["winning"]
    result["aggregate_service"]={"devices":2,"maximum_bad_motor_chains":1,
        "minimum_actual_delivery_per_tick":1,"general_bound":"M-p for M>p",
        "heat_bound":"8M for separate heat states; shared heat requires summed load bound"}
    paths=[Path(__file__),Path(__file__).with_name("Enactment.lean"),ROOT/"enforcement"/"finite_model.py"]
    result["source_sha256"]={path.relative_to(ROOT).as_posix():hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest() for path in paths}
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    parser.add_argument("--full-identities",action="store_true")
    parser.add_argument("--quick",action="store_true")
    args=parser.parse_args()
    if args.quick:
        value={"public":check_public_evidence(),"sources":check_sources(),
               "survival":check_survival_lemma(),"physics":check_physics(),
               "witnesses":protocol_witnesses(),"holding_cycle":holding_cycle(),"wrong_order":wrong_order_witness()}
    else:
        value=reproduce(args.full_identities)
    encoded=json.dumps(value,indent=2,sort_keys=True)+"\n"
    dest=Path(__file__).with_name("enactment_results.json")
    if args.write:
        if args.quick or args.full_identities:
            raise ValueError("Only the canonical complete report may be written")
        dest.write_text(encoded,encoding="utf-8")
        print("Wrote",dest)
    elif args.check:
        assert dest.read_text(encoding="utf-8").replace("\r\n","\n")==encoded,"Stored result mismatch"
        print("Enactment report reproduced exactly")
    else:
        print(encoded,end="")

if __name__=="__main__":
    main()
