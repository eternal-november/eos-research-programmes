#!/usr/bin/env python3
"""Compile the preserved sufficiency proof, then the separate iff extension."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

HERE=Path(__file__).resolve().parent
BASE_SHA='2bce2dd651117adf12e29edf967f91422cf0aea422549552063ec4a1e8f1e57a'

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean',default=os.environ.get('LEAN_BIN') or shutil.which('lean') or 'lean')
    args=parser.parse_args(); build=HERE/'.build';build.mkdir(exist_ok=True)
    env=dict(os.environ);env['LEAN_PATH']=str(build)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(source,extra=()):
        p=subprocess.run([args.lean,*map(str,extra),str(source)],capture_output=True,text=True,env=env,cwd=HERE)
        log=(p.stdout+p.stderr).replace(str(HERE)+os.sep,'')
        source.with_suffix('.lean.log').write_text(log)
        return p.returncode,log
    version=subprocess.run([args.lean,'--version'],capture_output=True,text=True)
    assert version.returncode==0
    base=HERE/'ResourceObservation.lean';source=HERE/'ResourceObservationIff.lean'
    assert hashlib.sha256(base.read_bytes()).hexdigest()==BASE_SHA
    base_rc,base_log=run(base,('-o',build/'ResourceObservation.olean'))
    assert base_rc==0,base_log
    assert base_log.count('does not depend on any axioms')==10
    rc,log=run(source,('-o',build/'ResourceObservationIff.olean'));assert rc==0,log
    assert log.count('does not depend on any axioms')==7
    audit_rc,audit_log=run(HERE/'AuditSignatures.lean')
    assert audit_rc==0,audit_log
    assert audit_log.count('does not depend on any axioms')==3
    negative=HERE/'negative_tests';negative.mkdir(exist_ok=True)
    bad=negative/'drop_monotone_transport.lean'
    text=source.read_text().replace("trans (mono hax' hcy') hsum",'hsum',1)
    assert text!=source.read_text();bad.write_text(text)
    bad_rc,bad_log=run(bad);assert bad_rc!=0,bad_log
    report={'lean_version':version.stdout.strip(),'base_source_sha256':BASE_SHA,'iff_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'base_axiom_free_declarations':10,'additional_axiom_free_declarations':7,'compile_exit_codes':[base_rc,rc],'elaborated_definition_and_signature_audit_exit_code':audit_rc,'negative_test':{'mutation':'Drop the monotone factor transport in necessity','exit_code':bad_rc,'rejected':True},'kind':'separate_hand_written_iff_formalization_not_generated_certificate_replay'}
    (HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
