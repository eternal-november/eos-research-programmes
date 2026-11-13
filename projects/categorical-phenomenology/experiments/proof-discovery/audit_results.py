"""Validate all emitted proof bundles and audit intermediate-lemma reuse."""
import collections,json
from pathlib import Path
import kernel
from experiment import fixed_cases,size
P=Path(__file__).parent

def rule_refs(cert):
    if isinstance(cert,dict):
        out={cert['rule']} if 'rule' in cert else set()
        for v in cert.values():out |= rule_refs(v)
        return out
    if isinstance(cert,list):return set().union(*(rule_refs(v) for v in cert)) if cert else set()
    return set()

def audit():
    frozen=json.loads((P/'fixed_cases_before_run.json').read_text())
    current=[{'name':n,'equation':e,'split':s} for n,e,s in fixed_cases()]
    assert json.dumps(frozen,sort_keys=True)==json.dumps(current,sort_keys=True),'Original workload changed'
    strict={n for n,e,s in fixed_cases() if s=='transfer' and max(map(size,e))>5}
    verified=[];reuse=[]
    for fp in sorted((P/'results').glob('*_proofs.json')):
        b=json.loads(fp.read_text()); v=kernel.check_bundle(b);v['file']=fp.name;verified.append(v)
        lib={e['name']:e for e in b['library']}
        for p in b['proofs']:
            if p['name'] not in strict:continue
            direct=rule_refs(p['certificate']);closure=set(direct);pending=list(direct)
            while pending:
                rule=pending.pop()
                if rule not in lib:continue
                new=rule_refs(lib[rule]['certificate'])-closure;closure|=new;pending.extend(new)
            reused=sorted(x for x in direct if x in lib and x!='training_cached')
            overlap=any(p['equation']==e['equation'] for e in lib.values())
            assert not overlap,'Compositional subset overlaps a library statement'
            reuse.append({'file':fp.name,'theorem':p['name'],'direct_intermediate_lemmas':reused,'direct_rules':sorted(direct),'transitive_dependencies':sorted(closure),'exact_library_overlap':overlap})
    for fp in sorted((P/'results').glob('cold_*.json')):
        if fp.name.endswith('_proofs.json'):continue
        run=json.loads(fp.read_text())
        for i,b in enumerate(run.get('cold_bundles',[])):
            v=kernel.check_bundle(b);v['file']=f'{fp.name}:cold_bundles[{i}]';verified.append(v)
    result={'original_workload_unchanged':True,'compositional_names':sorted(strict),'bundles_checked':len(verified),'bundle_checks':verified,'compositional_proof_audits':reuse}
    (P/'results'/'proof_and_reuse_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'original_workload_unchanged':True,'compositional_cases':len(strict),'bundles_checked':len(verified),'compositional_proofs_audited':len(reuse)}))

if __name__=='__main__':audit()
