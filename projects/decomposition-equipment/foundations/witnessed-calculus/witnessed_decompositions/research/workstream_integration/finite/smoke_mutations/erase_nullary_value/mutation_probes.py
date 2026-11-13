#!/usr/bin/env python3
"""Targeted mutated-copy probes; failures are expected and explicitly classified."""
import check_integration as d
from model import *
from pathlib import Path
import sys,json,hashlib

def expect_rejection(fn,message):
    try:fn()
    except AssertionError as e:
        assert str(e)==message,(str(e),message)
        return str(e)
    raise AssertionError('expected targeted rejection did not occur')

def main():
    name=sys.argv[1];rows=[]
    if name=='omit_MIn':
        assert 'MIn' not in MIXED_SCHEMAS
        for M in MONOIDS:
            x=L(Graph(1),Arrow(0,1));dx=D(0,x)
            msg='MIn certificate not admitted by syntactic basis'
            expect_rejection(lambda:d.check_paths(x,(Raw((dx,)),Eq(x,(),'D0')),(Raw((x,)),),M,'MIn_targeted_bare'),msg)
            empty=L(Graph(0),Arrow(1,1));host=C(Graph(1),(0,),x,empty)
            expect_rejection(lambda:d.check_paths(host,(Raw((dx,empty)),Eq(host,(0,),'D0')),(Raw((x,empty)),),M,'MIn_targeted_context'),msg)
            rows.append({'monoid':M.name,'bare_rejected':True,'contextual_rejected':True})
            components=leaves(d.six_term(M))+(L(Graph(0),Arrow(1,1)),)
            for slot,source in enumerate(components):
                weights=[];forests=[]
                for h in range(9):
                    t=source
                    for _ in range(h):t=D(0,t)
                    path=(Raw((t,)),)+d.eq_trace(t,M)
                    F,end=path_normalize(source,path,M);sem,semend=semantic_path(source,path,M)
                    assert end==semend==source and sem==(flat_identity(source.graph,source.arrow),)
                    assert node_count(F[0])==h
                    weights.append(node_count(F[0]));forests.append(F)
                assert weights==list(range(9)) and len(set(forests))==9
                rows.append({'monoid':M.name,'source_slot':slot,'raw_added_weights':weights,'semantic_tuple':'identity','scope':'finite illustration; necessity theorem is P'})
    elif name=='erase_nullary_value':
        for M in MONOIDS:
            for v in range(1,M.size):
                source=L(Graph(1),Arrow(0,1));l=C(Graph(1),(),D(v,U(0)),source)
                r=apply_step(l,(),'DL',M)
                # First verify the actual typed MIn path independently of recursive evaluation.
                d.check_paths(source,(Raw((l,)),Eq(r,(),'DL')),(Raw((r,)),),M,'MIn_targeted_unit')
                def local_value_check():
                    assert evaluation(l,M)==address_evaluation(l,M),'decorated-nullary MIn entry evaluation mismatch'
                expect_rejection(local_value_check,'decorated-nullary MIn entry evaluation mismatch')
                assert address_evaluation(l,M).value==address_evaluation(r,M).value==v
                rows.append({'monoid':M.name,'value':v,'typed_MIn_unit_path_checked':True,'independent_value':v,'intended_recursive_value_mismatch_detected':True})
    else:raise AssertionError('targeted probe only defined for the two required mutants')
    result={'status':'PASS','mutant':name,'kind':'TARGETED_MUTATED_COPY_PROBES','rows':rows,'model_sha256':hashlib.sha256(Path(__file__).with_name('model.py').read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).with_name('check_integration.py').read_bytes()).hexdigest()}
    Path(__file__).with_name('TargetedProbe.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
