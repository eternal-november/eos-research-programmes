"""Installed role transition, plus a slot-first reference for the frozen cut."""
from itertools import product, permutations
import json

def rules(pocket, holder):
    return {
        'first-close': ('A2','D2') if pocket == 'intact' else ('D2',),
        'gate-ticket': (holder+'2',),
        'relay2': ('C2','D2'),
        'second-close': ('D3',),
        'relay3': ('C3','D3'),
    }

def witness(pocket, holder):
    eligible=rules(pocket,holder)
    for sites in product(*eligible.values()):
        if len(set(sites))==len(sites):
            return dict(zip(eligible,sites))

def oracle(pocket, holder):
    slots=('A2','B2','C2','D2','C3','D3')
    for a,g,r,b,s in permutations(slots,5):
        if (a in (('A2','D2') if pocket=='intact' else ('D2',))
                and g==holder+'2' and r in ('C2','D2')
                and b=='D3' and s in ('C3','D3')):
            return True
    return False

def run(pocket, b_relay_failed, signed_successor, full_ledger):
    trace=[]
    def emit(*row): trace.append(row)
    holder,epoch='A',0
    pending={}
    def admit(t, actor, generation, job):
        ok=(actor,generation)==(holder,epoch) and job not in pending
        emit(t,'admit',actor,generation,job,ok)
        if ok:
            pending[job]=actor if job=='gate-ticket' else 'named-close'
        return ok
    assert admit(0,'A',0,'first-close')
    emit(0,'relay','D')
    # Planned A=>B is authorized and acknowledged; no holder-bound duty
    # is pending, and the first closure keeps its own permit.
    assert pending == {'first-close':'named-close'}
    holder,epoch='B',1
    emit(1,'planned-commit','A','B',epoch)
    assert admit(1,'B',1,'second-close')
    assert admit(1,'B',1,'gate-ticket')
    emit(1,'relay','C+D')
    # Same missing report under either true relay state. The isolated gate
    # actuator is independently certified functional, including in failure.
    emit(2,'notice','B-relay-report-missing',pocket)
    live_ids=tuple(sorted(pending))
    prepared=(signed_successor and full_ledger and witness(pocket,'C') is not None)
    reasons=(signed_successor,full_ledger,witness(pocket,'C') is not None)
    emit(2,'prepare','B','C',live_ids,reasons)
    if prepared:
        # Consume signed acceptance of the identity-bound outstanding ticket
        # in the same resource-side commit that advances epoch and swaps its
        # bearer. No external operation can interleave these writes.
        assert pending['gate-ticket']=='B'
        holder,epoch='C',2
        pending['gate-ticket']='C'
        emit(2,'commit-and-transfer','B','C',epoch,'gate-ticket')
    else:
        emit(2,'defer','B','C',epoch)
    assert not admit(2,'A',0,'queued-older-request')
    if prepared: assert not admit(2,'B',1,'queued-precommit-request')
    plan=witness(pocket,holder)
    assert plan is not None and len(set(plan.values()))==len(plan)
    for job,slot in plan.items():
        actor,tick=slot[0],int(slot[1])
        if tick != 2: continue
        if job.startswith('relay'):
            assert actor in ('C','D')  # actually works under both completions
            emit(2,'relay',actor)
        else:
            if job=='gate-ticket': assert pending[job]==actor==holder
            else: assert pending[job]=='named-close'
            del pending[job]
            emit(2,'settle',job,actor)
    assert pending == {'second-close':'named-close'}
    if not prepared and signed_successor and full_ledger:
        # Deferred commit: the incumbent-only ticket has now settled. The
        # second closure still survives the change on its independent permit.
        holder,epoch='C',2
        emit(3,'commit-after-discharge','B','C',epoch)
        assert not admit(3,'B',1,'queued-precommit-request')
    for job,slot in plan.items():
        actor,tick=slot[0],int(slot[1])
        if tick != 3: continue
        if job.startswith('relay'): emit(3,'relay',actor)
        else:
            assert pending.pop(job)=='named-close'
            emit(3,'settle',job,actor)
    assert not pending
    assert {e[0] for e in trace if e[1]=='relay'} == {0,1,2,3}
    return {'early':prepared,'final_holder':holder,'trace':trace,
            'unseen_actual_B_relay_failure':b_relay_failed}

def main():
    for pocket,holder in product(('intact','damaged'),('B','C')):
        assert bool(witness(pocket,holder))==oracle(pocket,holder)
    rows={}
    for p,s,f in product(('intact','damaged'),(False,True),(False,True)):
        a,b=(run(p,z,s,f) for z in (False,True))
        assert a['trace']==b['trace']
        assert a['early'] == (p=='intact' and s and f)
        assert a['final_holder']==('C' if s and f else 'B')
        rows[f'{p}-signature={s}-ledger={f}']=[a,b]
    print(json.dumps(rows,indent=2,sort_keys=True))
if __name__=='__main__': main()
