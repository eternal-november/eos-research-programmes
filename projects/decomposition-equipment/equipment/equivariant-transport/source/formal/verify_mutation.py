#!/usr/bin/env python3
"""Require Lean to reject an incorrectly covariant inverse-coordinate action."""
import hashlib,json,pathlib,subprocess,sys,tempfile
root=pathlib.Path(__file__).resolve().parent
source=(root/'D1FiniteTypedAction.lean').read_text()
old='fun x y => R ((p a).backward x) ((p b).backward y)'
new='fun x y => R ((p a).forward x) ((p b).forward y)'
if source.count(old)!=1: raise RuntimeError('mutation anchor not unique')
with tempfile.TemporaryDirectory(prefix='d1-negative-',dir=root) as tmp:
    mutant=pathlib.Path(tmp)/'Mutant.lean'
    mutant.write_text(source.replace(old,new))
    p=subprocess.run([sys.argv[1],str(mutant)],cwd=root,text=True,capture_output=True)
    output=p.stdout+p.stderr
    if p.returncode==0 or 'error:' not in output:
        raise RuntimeError('Lean did not reject wrong-coordinate action')
    # Keep concise diagnostics, not a misleading successful-build transcript.
    (root/'mutation_rejection.log').write_text(output)
    result={'status':'PASS','mutant_exit_code':p.returncode,'mutation':'inverse coordinate replaced with forward coordinate',
            'original_sha256':hashlib.sha256(source.encode()).hexdigest(),
            'mutant_sha256':hashlib.sha256(mutant.read_bytes()).hexdigest(),
            'first_error':next(x for x in output.splitlines() if 'error:' in x).replace(str(mutant), 'Mutant.lean')}
    (root/'mutation_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
