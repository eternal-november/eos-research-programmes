"""Audit-only regeneration of compressed causal calibration traces. Not learner input."""
import json,hashlib
from pathlib import Path
import numpy as np
from experiment import World,E,REF

def main():
    root=Path(__file__).parent/'results';data=json.loads((root/'results.json').read_text());passed=[]
    for row in data['family_runs']:
        archive=json.loads((root/f"{row['id']}_evidence.json").read_text())
        _,N,digest,meta=archive[-1]
        w=World(row['n'],row['seed'],row['sharing_world_audit_only'])
        w.rng.bit_generator.state=meta['bit_generator_state'];b=int(max(w.blocks))+1
        category=(1-w.rng.binomial(2,w.p,size=(N,b)).astype(np.int8))[:,w.blocks]
        reference_error=(w.rng.uniform(-REF,REF,(N,b))+w.rng.uniform(-REF,REF,(N,b)))/2
        residual=category*E-reference_error[:,w.blocks]
        decoded=np.rint(residual/E).astype(np.int8)
        assert hashlib.sha256(residual.tobytes()).hexdigest()==meta['residual_sha256']
        assert hashlib.sha256(decoded.tobytes()).hexdigest()==digest
        assert np.array_equal(decoded,np.load(root/meta['decoded_observations_file'])['categories'])
        # The actual physical reference is .25+error per sample; packet .25+category*E.
        # All channels are idle; at most5 reports/FIFO at each calibration endpoint.
        trace=w.queue_trace([(i,0) for i in range(w.n)])
        assert max(t[3] for t in trace)<=5<10
        passed.append(row['id'])
    result={'calibration_exact_observation_regenerations':len(passed),'queue_idle_template_checks':len(passed),
            'auditor_only_world_truth_not_certificate_input':True,'cases':passed}
    (root/'replay_checks.json').write_text(json.dumps(result,indent=2));print(result)
if __name__=='__main__':main()
