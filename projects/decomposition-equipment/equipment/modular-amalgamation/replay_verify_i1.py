#!/usr/bin/env python3
"""Check delivered source pins, extract an isolated snapshot and replay regressions.

The mathematical verifier is unmodified. This delivery wrapper uses relative
paths and temporary archives only; it does not reproduce imported old proofs.
"""
import hashlib,json,pathlib,py_compile,subprocess,sys,tempfile,zipfile
R=pathlib.Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    pins=json.loads((R/'verify_i1_sourcepins.json').read_text())
    for group in pins.values():
        for name,digest in group.items():assert sha(R/name)==digest, 'source pin differs: '+name
    names=sorted({name for group in pins.values() for name in group})
    scripts={'verify_i1.py':'verify_i1_results.json','verify_graph_fixture.py':'verify_graph_fixture.json','verify_interface_pushout.py':'verify_interface_pushout.json','verify_twisted_normal_forms.py':'verify_twisted_normal_forms.json','audit_failure.py':'audit_failure_results.json'}
    with tempfile.TemporaryDirectory(prefix='i1_replay_') as tmp:
        tmp=pathlib.Path(tmp); archive=tmp/'snapshot.zip'; d=tmp/'extracted'
        with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
            for name in names:z.write(R/name,name)
        with zipfile.ZipFile(archive) as z:z.extractall(d)
        for name in names:assert (d/name).read_bytes()==(R/name).read_bytes()
        for name in names:
            if name.endswith('.py'):py_compile.compile(str(d/name),doraise=True)
        checks={}
        for script,result in scripts.items():
            expected=json.loads((R/result).read_text())
            p=subprocess.run([sys.executable,str(d/script)],cwd=d,capture_output=True,text=True,check=True)
            actual=json.loads(p.stdout) if script=='audit_failure.py' else json.loads((d/result).read_text())
            assert actual==expected, 'replay result differs: '+script
            checks[script]={'status':'PASS','all_result_fields_identical':True}
        for group in pins.values():
            for name,digest in group.items():assert sha(R/name)==digest, 'source changed during replay: '+name
        report={'status':'PASS','byte_identical_extracted_sources':len(names),'checks':checks,'sourcepins_sha256':sha(R/'verify_i1_sourcepins.json'),'limit':'Finite regressions only; imported mathematical proofs are source dependencies, not reproduced computationally.'}
        (R/'verify_i1_replay_report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report,indent=2))
if __name__=='__main__':main()
