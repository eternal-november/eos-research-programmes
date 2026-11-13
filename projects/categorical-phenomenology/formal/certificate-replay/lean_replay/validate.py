#!/usr/bin/env python3
"""Rebuild every original saved bundle and check emitted proofs with Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import shutil
import re
import subprocess
import sys
import time
from pathlib import Path
import translate

HERE=Path(__file__).resolve().parent
EXPERIMENT=HERE.parent/'experiment'
DEFAULT_LEAN=Path(os.environ.get('LEAN_BIN') or shutil.which('lean') or 'lean')
_LEAN_FOR_LOG=str(DEFAULT_LEAN)

def sha(raw): return hashlib.sha256(raw).hexdigest()
def checked(cmd,cwd=None):
    p=subprocess.run(list(map(str,cmd)),cwd=cwd,capture_output=True,text=True)
    def portable(value):
        value=str(value).replace(str(HERE.parent)+os.sep,'')
        if Path(_LEAN_FOR_LOG).is_absolute(): value=value.replace(_LEAN_FOR_LOG,'<LEAN_BIN>')
        return value
    commands=['python' if str(x)==sys.executable else portable(x) for x in cmd]
    return {'command':commands, 'exit_code':p.returncode, 'stdout':portable(p.stdout), 'stderr':portable(p.stderr)}

def expected_trace(bundle):
    expected=[]
    for e in bundle['library']+bundle['proofs']:
        c=e['certificate']
        branches=[('rewrite',c)] if c['mode']=='rewrite' else [('base',c['base']),('step',c['step'])]
        for branch,c in branches:
            for side in ('left','right'):
                for i,s in enumerate(c[side]):
                    expected.append((e['name'],branch,side,i,s['rule'],s.get('direction',1),s['path']))
    return expected

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--lean',type=Path,default=DEFAULT_LEAN)
    args=p.parse_args()
    global _LEAN_FOR_LOG
    _LEAN_FOR_LOG=str(args.lean)
    out=HERE/'checked'; out.mkdir(exist_ok=True)
    report={'lean_version':checked([args.lean,'--version']), 'bundles':[], 'negative_lean_tests':[], 'generic_translation_fixtures':[]}
    assert report['lean_version']['exit_code']==0
    tests=checked([sys.executable,'-m','unittest','test_translate','-v'],HERE)
    (HERE/'translation_tests.log').write_text(tests['stdout']+tests['stderr'])
    report['translation_tests']=tests; assert tests['exit_code']==0
    originals=sorted((EXPERIMENT/'results').glob('*_proofs.json'))
    initial={str(p):sha(p.read_bytes()) for p in originals}
    for path in originals:
        raw=path.read_bytes(); bundle=json.loads(raw)
        lean_text,trace=translate.translate_bytes(raw)
        actual=[tuple(s[k] for k in ('entry','branch','side','index','rule','direction','path')) for s in trace['steps']]
        assert actual==expected_trace(bundle)
        assert trace['source_sha256']==sha(raw)
        code='\n'.join(line.split('--',1)[0] for line in lean_text.splitlines())
        assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',code)
        stem=path.stem.removesuffix('_proofs'); leanfile=out/(stem+'.lean')
        leanfile.write_text(lean_text); leanfile.with_suffix('.trace.json').write_text(json.dumps(trace,indent=2)+'\n')
        start=time.monotonic(); result=checked([args.lean,leanfile]); elapsed=time.monotonic()-start
        leanfile.with_suffix('.lean.log').write_text(result['stdout']+result['stderr'])
        decls=len(trace['declarations'])
        assert result['exit_code']==0,(path,result)
        assert result['stdout'].count('does not depend on any axioms')==decls
        assert not result['stderr']
        report['bundles'].append({'source':str(path.relative_to(EXPERIMENT)),'source_sha256':sha(raw),'lean_file':str(leanfile.relative_to(HERE)),'lean_sha256':sha(lean_text.encode()),'trace_sha256':sha(leanfile.with_suffix('.trace.json').read_bytes()),'counts':trace['counts'],'exit_code':result['exit_code'],'axiom_free_declarations':decls,'certificate_trace_identity':True,'elapsed_seconds':elapsed})
    # These are translator coverage fixtures, not newly discovered theorems.
    fixture_dir=HERE/'generic_fixtures'; fixture_dir.mkdir(exist_ok=True)
    X=['v','X']; elem=['e','X']; nil=['nil']; term=['app',X,['cons',elem,nil]]
    symmetric={'library':[], 'proofs':[{'name':'reverse_direction','equation':[X,['app',nil,X]],'certificate':{'mode':'rewrite','left':[{'rule':'app_nil','path':[],'direction':-1}],'right':[]}}]}
    generalized={'library':[], 'proofs':[{'name':'generalized_element_same_spelling','equation':[term,term],'certificate':{'mode':'induction','variable':'X','tail':'freshTail','head':'freshHead','base':{'left':[],'right':[]},'step':{'left':[{'rule':'app_cons','path':[]},{'rule':'IH','path':[2]}],'right':[{'rule':'app_cons','path':[]}]}}}]}
    renamed=json.loads((EXPERIMENT/'results/guided_10000000_proofs.json').read_text())
    def rename_term(t):
        if t[0] in ('v','e'): return [t[0], 'fresh_'+t[1]]
        return [t[0], *(rename_term(x) for x in t[1:])]
    for entry in renamed['library']+renamed['proofs']:
        entry['equation']=list(map(rename_term,entry['equation']))
        c=entry['certificate']
        if c['mode']=='induction':
            for key in ('variable','tail','head'): c[key]='fresh_'+c[key]
    fixtures={'reverse_direction':symmetric,'generalized_element_same_spelling':generalized,'alpha_renamed_guided':renamed}
    for name,bundle in fixtures.items():
        raw=(json.dumps(bundle,indent=2)+'\n').encode(); source=fixture_dir/(name+'.json'); source.write_bytes(raw)
        lean_text,trace=translate.translate_bytes(raw); path=source.with_suffix('.lean'); path.write_text(lean_text)
        result=checked([args.lean,path]); assert result['exit_code']==0,(name,result)
        assert result['stdout'].count('does not depend on any axioms')==len(trace['declarations'])
        path.with_suffix('.lean.log').write_text(result['stdout']+result['stderr'])
        report['generic_translation_fixtures'].append({'name':name,'exit_code':result['exit_code'],'axiom_free_declarations':len(trace['declarations'])})
    guided=(out/'guided_10000000.lean').read_text()
    mutations={
        'wrong_ih_parameter': guided.replace('(ih (v_Y := (List.cons e__a v_Y)))','(ih (v_Y := v_Y))',1),
        'replace_general_ih_with_reflexivity': guided.replace('(ih (v_Y := (List.cons e__a v_Y)))','(Eq.refl (rev (app (rev v__t) (List.cons e__a v_Y))))',1),
        'wrong_reused_lemma_argument': guided.replace('(lib_lemma_003 (α := α) (v_X := (app v_X v_Y)) (v_Y := v_Z))','(lib_lemma_003 (α := α) (v_X := v_X) (v_Y := v_Z))',1),
    }
    rejected=HERE/'negative_tests';rejected.mkdir(exist_ok=True)
    for name,text in mutations.items():
        assert text!=guided,name
        path=rejected/(name+'.lean');path.write_text(text)
        result=checked([args.lean,path]);assert result['exit_code']!=0,(name,result)
        path.with_suffix('.lean.log').write_text(result['stdout']+result['stderr'])
        report['negative_lean_tests'].append({'name':name,'exit_code':result['exit_code'],'rejected':True,'log':str(path.with_suffix('.lean.log').relative_to(HERE))})
    assert initial=={str(p):sha(p.read_bytes()) for p in originals}
    report['original_certificate_files_unchanged']=True
    report['totals']={'bundle_files':len(report['bundles']),'nonempty_bundle_files':sum(bool(b['counts']['library']+b['counts']['held_out']) for b in report['bundles']),'library_occurrences':sum(b['counts']['library'] for b in report['bundles']),'held_out_occurrences':sum(b['counts']['held_out'] for b in report['bundles']),'recorded_rewrite_step_occurrences':sum(b['counts']['recorded_rewrite_steps'] for b in report['bundles'])}
    report['all_checks_passed']=True
    (HERE/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report['totals'],indent=2));print('All validation checks passed.')
if __name__=='__main__': main()
