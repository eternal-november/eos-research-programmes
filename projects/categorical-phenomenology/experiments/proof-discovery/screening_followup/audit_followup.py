"""Audit frozen dependencies, generated labels, screening errors, and proofs."""
import hashlib,itertools,json
from pathlib import Path
import followup as f
import experiment as e
import kernel
P=Path(__file__).resolve().parent

def main():
    for manifest,base in [(P.parent/'FINAL_SOURCE_SHA256.txt',P.parent),(P/'FROZEN_SHA256.txt',P)]:
        for line in manifest.read_text().splitlines():
            h,name=line.split();assert hashlib.sha256((base/name).read_bytes()).hexdigest()==h
    allc=set(f.candidates(e.Cost(),343));smallc=set(f.candidates(e.Cost(),8));assert allc<=smallc
    values=[()]+[(x,) for x in [0,1]]+list(itertools.product([0,1],repeat=2));witnesses=[]
    for eq in sorted(smallc-allc,key=repr):
        for tup in itertools.product(values,repeat=3):
            env=dict(zip('XYZ',tup));cost=e.Cost()
            if e.eval_term(eq[0],env,cost)!=e.eval_term(eq[1],env,cost):
                witnesses.append({'equation':eq,'counterexample':env});break
        else:raise AssertionError('Additional candidate has no claimed counterexample')
    cases=json.loads((P/'workload.json').read_text());positives=[];negatives=[]
    for c in cases:
        lhs,rhs=map(kernel.freeze,c['equation'])
        assert e.size(lhs)>=9
        if c['expected']:
            assert f.normal_form(lhs)==rhs;positives.append(c['id'])
        else:
            env={name:tuple(v) if isinstance(v,list) else v for name,v in c['counterexample'].items()}
            assert f.semantic_eval(lhs,env)!=f.semantic_eval(rhs,env);negatives.append(c['id'])
    checked=[]
    for fp in sorted((P/'results').glob('*.json')):
        j=json.loads(fp.read_text())
        if not isinstance(j,dict) or 'bundle' not in j:continue
        k=kernel.check_bundle(j['bundle']);k['file']=fp.name;checked.append(k)
    identical={}
    for mode in ['generic','guided']:
        a=json.load(open(P/'results'/f'{mode}_screen343_complete.json'))
        b=json.load(open(P/'results'/f'{mode}_screen8_complete.json'))
        identical[mode]={'library_and_certificates_identical':a['bundle']['library']==b['bundle']['library'],'heldout_certificates_identical':a['bundle']['proofs']==b['bundle']['proofs'],'test_cost_equal':a['cost']['total']-a['acquisition']==b['cost']['total']-b['acquisition']}
        assert all(identical[mode].values())
    out={'dependencies_hash_verified':True,'positive_count':len(positives),'negative_counterexample_count':len(negatives),'all_screen_candidates':len(allc),'small_screen_candidates':len(smallc),'additional_false_candidates':len(witnesses),'all_additional_false_witnesses':witnesses,'final_equivalence':identical,'checked_bundles':checked}
    (P/'results'/'followup_audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS:',len(checked),'bundles;',len(witnesses),'additional candidates all falsified; same libraries and held-out certificates.')
if __name__=='__main__':main()
