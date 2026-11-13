"""Supplemental deterministic online regressions declared after main frozen runs.
Not new statistical outcomes. Detection/actuation timing is a supplied premise.
"""
import json
from pathlib import Path
import numpy as np
from experiment import World,Ledger

def pending_replacement(pending,ledger):
    # No implemented migration: refuse and preserve queue and all old token IDs.
    return not pending,list(pending),dict(ledger.charges)

def main():
    world=World(5,731,'global');u=np.ones(5);z=np.zeros(5)
    ledger=Ledger();tokens={(0,0,-2),(0,0,-1)};assert ledger.reserve(tokens,.023)
    ledger.expose(tokens);charged=ledger.used
    rows=[]
    for d in (.77,1.):
        first=world.state(u,z,d)
        # Explicit premise: invalidation delivered before second-slot actuation.
        tail=world.state(z,u,d);settled=world.state(z,z,d)
        assert max(map(np.max,[first,tail,settled]))<=1.5
        rows.append({'background':d,'detected_before_second_actuation':True,
            'peak':float(max(map(np.max,[first,tail,settled]))),'completed_two_slot_jobs':0,
            'interrupted_jobs':5,'risk_charge_retained':ledger.used,
            'status':'hard_envelope_stop_safe'})
        late=world.state(u,u,d)
        rows.append({'background':d,'detected_before_second_actuation':False,
            'second_slot_peak':float(max(late)),'status':'assurance_loss',
            'physical_violation':bool(max(late)>1.5),'risk_charge_retained':ledger.used})
    pending=[{'channel':0,'window':[-2,-1],'source_tokens':sorted(tokens),'generation':0}]
    accepted,after,charges=pending_replacement(pending,ledger)
    assert not accepted and after==pending and charges==ledger.charges and ledger.used==charged
    result={'declared_scope':'Supplemental deterministic regressions; no autonomous drift detector proved.',
       'hard_envelope_proof':'d<=1, first d+.5<=1.5, stop-tail d+.25<=1.25; stop must precede second actuation',
       'cases':rows,'nonempty_queue_replacement':'rejected_without_erasing_pending_ids',
       'evidence_retraction_note':'Restoration toggles in main benchmark model external revalidation; no false past evidence is repaired retroactively.'}
    (Path(__file__).parent/'results'/'online_regressions.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
