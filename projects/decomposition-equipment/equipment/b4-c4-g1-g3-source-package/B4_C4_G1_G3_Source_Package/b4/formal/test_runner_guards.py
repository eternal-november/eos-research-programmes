#!/usr/bin/env python3
"""Failure receipts and frozen-source guards, no recompilation needed."""
import pathlib,tempfile,shutil,subprocess,json,sys,hashlib
R=pathlib.Path(__file__).resolve().parent

def need(b,m):
 if not b:raise RuntimeError(m)
def main():
 (R/'guard_runs').mkdir(exist_ok=True);work=pathlib.Path(tempfile.mkdtemp(prefix='guards_',dir=R/'guard_runs'))
 source=work/'source';shutil.copytree(R/'original_source',source)
 (source/'WitnessedDecompositions/RawRefinement.lean').write_text((source/'WitnessedDecompositions/RawRefinement.lean').read_text()+'\n-- tampered guard fixture\n')
 cases=[]
 for optimization in ([],['-O'],['-OO']):
  out=work/('out'+str(len(optimization))+(optimization[0] if optimization else ''))
  out.mkdir();(out/'result.json').write_text('{"schema":"b4-formal-receipt-v1","status":"PASS"}\n')
  cmd=[sys.executable,*optimization,str(R/'verify_b4_lean.py'),'--source-root',str(source),'--output-dir',str(out)]
  r=subprocess.run(cmd,text=True,capture_output=True);receipt=json.loads((out/'result.json').read_text())
  need(r.returncode!=0 and receipt['status']=='FAIL' and 'original source byte mismatch' in receipt['error'],'tamper guard or stale PASS failure')
  cases.append({'optimization':optimization,'exit_code':r.returncode,'status':'REJECTED','receipt_status':receipt['status'],'reason':receipt['error']})
 result={'status':'PASS','tests':cases,'runner_sha256':hashlib.sha256((R/'verify_b4_lean.py').read_bytes()).hexdigest(),'guard_test_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
 (R/'guard_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
