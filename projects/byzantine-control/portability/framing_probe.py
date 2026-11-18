"""Source-bound framing probes. Component/certificate scope, not source defeat."""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from constructors import projected_support

HERE=Path(__file__).resolve().parent
LOCAL=HERE.parent/'local-control'
spec=importlib.util.spec_from_file_location('_portability_comparison',LOCAL/'primary_comparison_model.py')
cmp=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=cmp
spec.loader.exec_module(cmp)


def need(ok,reason):
    if not ok:raise AssertionError(reason)


def generate():
    source,sb=cmp.record_at(cmp.SOURCE,'port_source_results.json')
    resource,rb=cmp.record_at(cmp.RESOURCES,'port_resource_results.json')
    assembly,ab=cmp.record_at(cmp.ASSEMBLY,'primary_assembly_results.json')
    need(assembly['bindings']['source']['commit']==cmp.SOURCE,'Assembly source mismatch')
    need(assembly['bindings']['resources']['commit']==cmp.RESOURCES,'Assembly resource mismatch')
    pm,code,image=cmp.load_policy(source['base_binding']['commit'],source['base_binding']['image_sha256'])
    k=code.constants
    need(k['ORIGINS']==13,'Probe changed its thirteen-origin interface')
    actual=[]
    for bad in (0,6,7):
        machine=pm.Machine(code,poison=0);ports=pm.RawPorts(code)
        load_key=3+k['VIEW_WORDS']
        for origin in range(13):
            ports.fast[(origin,0,load_key)]=0 if origin<bad else 1100
            ports.fast[(origin,0,load_key+2)]=0
        machine.enter('permission',(k['TARGET_BASE'],0))
        need(machine.run(ports,until_yield=False)=='halt','Permission did not finish')
        need(machine.C==code.image,'Input-only test changed code')
        actual.append(dict(false_low_slots=bad,permission=machine.result(),instructions=machine.steps))
    need([row['permission'] for row in actual]==[0,0,1],'Shared-footprint component obstruction changed')
    footprints={i:{'guard':frozenset({i})} for i in range(6)}
    original=projected_support(range(6),footprints,'guard')
    footprints[0]['guard']=frozenset({0,6})
    modified=projected_support(range(6),footprints,'guard')
    need(len(original)==6 and len(modified)==7,'Footprint projection changed')
    age=Q(source['base_binding']['functional_guard_horizon'])
    drift=Q(source['mechanical']['force_continuation_drift'])
    multiplier=Q(source['mechanical']['force_continuation_multiplier'])
    raw_error=Q(1,100)
    intercept=multiplier*(Q(1,2)+raw_error)
    critical=(1-intercept)/drift
    later=critical+1
    bound=intercept+drift*age;late_bound=intercept+drift*later
    need(bound==Q(assembly['force_and_return']['guard_force_upper'])<1,'Original force certificate changed')
    need(late_bound>1,'Longer-age sufficient bound did not fail')
    owned=('FRAMINGS.md','framing_probe.py','constructors.py','CONSTRUCTORS.md')
    return dict(status='reproduced source-bound component and sufficient-certificate probes',
                bindings=dict(source=sb,resources=rb,assembly=ab),image_sha256=image,
                helper_sha256_lf={'../local-control/primary_comparison_model.py':sha256((LOCAL/'primary_comparison_model.py').read_bytes().replace(b'\r\n',b'\n')).hexdigest()},
                incidence=dict(original_slots=sorted(original),changed_slots=sorted(modified),tokens=6,
                               full_modified_hybrid_reachability_proved=False),
                actual_guard=actual,
                age=dict(original=str(age),original_bound=str(bound),critical=str(critical),
                         changed=str(later),changed_bound=str(late_bound),
                         changed_age_source_realized=False),
                source_inputs_sha256_lf={name:sha256((HERE/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest() for name in owned},
                program_completion=False,universal_impossibility=False,independent_review_separate=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write',action='store_true');modes.add_argument('--check',action='store_true')
    args=parser.parse_args();result=generate();path=HERE/'framing_results.json'
    if args.write:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8',newline='\n')
        print('Wrote source-bound framing probe record; program incomplete')
    else:
        need(json.loads(path.read_text(encoding='utf-8'))==result,'Framing probe record or binding differs')
        print('PASS matching framing probe record; program incomplete')


if __name__=='__main__':main()
