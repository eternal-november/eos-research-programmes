#!/usr/bin/env python3
"""Source-only E3 Lean replay; public pinned upstream cache is the only object reuse.
No network, downloaded objects, project-cache reuse, or optimization-sensitive assert.
"""
import argparse,datetime,hashlib,json,os,pathlib,re,shutil,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parent
DEFAULT=pathlib.Path('/workspace/shared/d1_equivariant_transport_20261031/formal/toolchain')
INPUTS=['E1RelationEquipment.lean','E1FiniteExamples.lean','E3GraphGroupoidCore.lean','E3FiniteExamples.lean','verify_fresh.py','README_FORMAL.md','P_CORE_ADAPTER.md','original_source_custody.json','test_formal_guards.py']
MODES={0:'normal',1:'optimized',2:'double-optimized'}
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def require(b,m):
    if not b: raise RuntimeError(m)
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def reject(m): print(json.dumps({'status':'REJECT','reason':m},sort_keys=True)); return 2
def no_symlinks(p):
    for x in [p,*p.parents]: require(not x.is_symlink(),f'symlink destination forbidden: {x}')
def input_paths():
    return [ROOT/x for x in INPUTS]+sorted(p for p in (ROOT/'original_source').rglob('*') if p.is_file())
def guard_output(p,inputs):
    p=pathlib.Path(os.path.abspath(p)); no_symlinks(p)
    require(not p.is_relative_to(ROOT) or p.is_relative_to(ROOT/'evidence'),'output would overwrite protected source tree')
    require(p.name.endswith('.json'),'output must be a JSON receipt')
    if p.exists():
        require(p.is_file(),'output is not a regular file')
        require(p.stat().st_nlink==1,'hardlinked output forbidden')
        existing=json.loads(p.read_text())
        require(existing.get('schema')=='e3-formal-receipt-v1','existing destination is not this runner’s receipt')
        for q in inputs+[ROOT/'source_freeze.json']:
            require(not q.exists() or not os.path.samefile(p,q),'output aliases protected source')
    return p

def main():
    ap=argparse.ArgumentParser(exit_on_error=False)
    ap.add_argument('--toolchain',type=pathlib.Path,default=DEFAULT/'lean-4.35.0-linux')
    ap.add_argument('--upstream-project',type=pathlib.Path,default=DEFAULT/'project')
    ap.add_argument('--output',type=pathlib.Path,default=ROOT/'evidence/fresh_result.json')
    ap.add_argument('--work-parent',type=pathlib.Path,default=ROOT/'runs')
    ap.add_argument('--mode',choices=list(MODES.values()))
    args=ap.parse_args(); t0=time.monotonic(); started=utc()
    paths=input_paths(); output=guard_output(args.output,paths)
    actual_mode=MODES.get(sys.flags.optimize)
    require(actual_mode is not None,'unsupported optimization mode')
    require(args.mode is None or args.mode==actual_mode,'requested mode differs from Python runtime')
    work=pathlib.Path(os.path.abspath(args.work_parent)); no_symlinks(work)
    require(not work.is_relative_to(ROOT) or work.is_relative_to(ROOT/'runs'),'work-parent would modify protected source tree')
    require(work!=ROOT/'runs' or not work.exists() or work.is_dir(),'invalid work-parent')
    require(not any(p.suffix in ('.olean','.ilean','.ir') for p in paths),'bundled originals not source-only')
    require(all(not p.is_symlink() for p in paths),'symlink source forbidden')
    before={str(p.relative_to(ROOT)):sha(p) for p in paths}
    manifest=json.loads((ROOT/'source_freeze.json').read_text())
    require(manifest['schema']=='e3-formal-source-freeze-v1','wrong manifest schema')
    require(manifest['sources']==before,'frozen source hash/set mismatch')
    freeze_hash=sha(ROOT/'source_freeze.json')
    lock=json.loads((ROOT/'original_source/lake-manifest.json').read_text())
    require(sha(ROOT/'original_source/lake-manifest.json')=='0e4afebb985207e83e2a2fdf3d42281f9986e939ebc31084eaa5f8c3479c22cc','original dependency lock changed')
    require((ROOT/'original_source/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0','toolchain pin changed')
    env=dict(os.environ);env['PATH']=str(args.toolchain.resolve()/'bin')+os.pathsep+env['PATH'];env.pop('LEAN_PATH',None)
    compiler=subprocess.check_output([str(args.toolchain/'bin/lean'),'--version'],text=True,env=env).strip()
    require('version 4.35.0' in compiler and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in compiler,'compiler version/commit mismatch')
    pins=[]
    for d in lock['packages']:
        path=args.upstream_project/'.lake/packages'/d['name']
        rev=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        require(rev==d['rev'],f"wrong public upstream pin: {d['name']}")
        clean=subprocess.run(['git','-C',str(path),'diff','--quiet','HEAD','--']).returncode==0
        require(clean,f"modified tracked upstream source: {d['name']}")
        pins.append({'name':d['name'],'expected':d['rev'],'actual':rev,'tracked_source_clean':True})
    work.mkdir(parents=True,exist_ok=True);run=pathlib.Path(tempfile.mkdtemp(prefix='fresh_e3_',dir=work));project=run/'project'
    shutil.copytree(ROOT/'original_source',project)
    (project/'.lake/packages').mkdir(parents=True)
    for d in lock['packages']:
        (project/'.lake/packages'/d['name']).symlink_to((args.upstream_project/'.lake/packages'/d['name']).resolve(),target_is_directory=True)
    aliases={'GraphCoordinates.lean':'research/workstream_A/rewrite/GraphCoordinates.lean','GraphCutFragment.lean':'research/workstream_C1/lean/GraphCutFragment.lean','GraphCutAxioms.lean':'research/workstream_C1/lean/GraphCutAxioms.lean'}
    for dst,src in aliases.items():shutil.copy2(project/src,project/dst)
    newmodules=['E1RelationEquipment','E1FiniteExamples','E3GraphGroupoidCore','E3FiniteExamples']
    for name in newmodules:shutil.copy2(ROOT/(name+'.lean'),project/(name+'.lean'))
    inherited=[str(p.relative_to(project)) for p in project.rglob('*.olean') if '.lake/packages/' not in str(p)]
    require(not inherited,'inherited project object files detected')
    originals={str(p.relative_to(ROOT/'original_source')):sha(p) for p in (ROOT/'original_source').rglob('*') if p.is_file()}
    require(all(sha(project/rel)==h for rel,h in originals.items()),'copied original bytes differ')
    stages=[];closures={}
    def stage(name,cmd,success=True):
        log=run/(name+'.log')
        with log.open('w') as out:r=subprocess.run(cmd,cwd=project,env=env,stdout=out,stderr=subprocess.STDOUT)
        text=log.read_text()
        stages.append({'name':name,'command':cmd,'returncode':r.returncode,'log':str(log),'log_sha256':sha(log)})
        if success:
            require(r.returncode==0,f'{name} failed: {log}')
            require('sorryAx' not in text and 'declaration uses `sorry`' not in text,f'{name} contains proof holes')
        return r.returncode,text
    targets=['WitnessedDecompositions']+['WitnessedDecompositions.'+p.stem for p in sorted((ROOT/'original_source/WitnessedDecompositions').glob('*.lean'))]
    stage('original_build',['lake','build',*targets])
    def compile_module(name,label=None,success=True):
        obj=project/'.lake/build/lib/lean'/pathlib.Path(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        return stage(label or name.replace('/','_'),['lake','env','lean','-o',str(obj.relative_to(project)),name+'.lean'],success)
    for name in ['GraphCoordinates','GraphCutFragment','GraphCutAxioms','research/workstream_C2/lean/RelationInterface',*newmodules]:
        _,out=compile_module(name)
        require('warning:' not in out,f'warning in final module: {name}')
        for m in re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",out,re.S):
            ax=[] if m[2] is None else [x.strip() for x in m[2].split(',')]
            require(set(ax)<={'propext','Classical.choice','Quot.sound'},f'unexpected axioms: {ax}')
            closures[m[1]]=ax
    require(len(closures)>=100,'incomplete transitive axiom closure audit')
    core=(ROOT/'E3GraphGroupoidCore.lean').read_text()
    examples=(ROOT/'E3FiniteExamples.lean').read_text()
    mutations=[
      ('drop_inverse','⟨H.graph, g⁻¹ * H.grade * f⟩','⟨H.graph, g * H.grade * f⟩'),
      ('reverse_boundary_order','⟨H.graph, g⁻¹ * H.grade * f⟩','⟨H.graph, f * H.grade * g⁻¹⟩'),
      ('erase_cartesian_scalar','toFun α := ⟨α.cut, α.weight, by','toFun α := ⟨α.cut, 0, by'),
      ('erase_primitive_scalar','refine ⟨b.cut,b.weight,?_⟩','refine ⟨b.cut,0,?_⟩'),
      ('erase_coordinate_lift','(fun i => (treeBlocks (children i)).map (GraphCut.liftBlock (generatorBlock g i)))','(fun i => treeBlocks (children i))')]
    mresults=[]
    for name,old,new in mutations:
        require(core.count(old)==1,f'nonunique mutation target: {name}')
        mutant=core.replace(old,new,1);(project/'E3GraphGroupoidCore.lean').write_text(mutant)
        rc,out=compile_module('E3GraphGroupoidCore','mutation_'+name,False)
        where='core'
        if rc==0:
            rc,out=compile_module('E3FiniteExamples','mutation_'+name+'_examples',False);where='finite_examples'
        require(rc!=0 and 'error:' in out,f'mutant survived: {name}')
        require(not any(x in out for x in ['unknown module','must be contained in root directory','object file does not exist']),f'infrastructure rejection: {name}')
        mresults.append({'name':name,'source_sha256':hashlib.sha256(mutant.encode()).hexdigest(),'status':'REJECTED','returncode':rc,'rejected_by':where})
    (project/'E3GraphGroupoidCore.lean').write_text(core)
    compile_module('E3GraphGroupoidCore','restore_checked_core')
    # A correctly typed but occurrence-collapsing source mutation must fail concrete full-cut claims.
    old='secondReplacement (.leaf c3)))';new='firstReplacement (.leaf c3)))'
    require(examples.count(old)==1,'nonunique occurrence mutation target')
    mutant=examples.replace(old,new,1);(project/'E3FiniteExamples.lean').write_text(mutant)
    rc,out=compile_module('E3FiniteExamples','mutation_collapse_repeated_occurrence',False)
    require(rc!=0 and 'error:' in out and 'unknown module' not in out,'occurrence mutant not semantically rejected')
    mresults.append({'name':'collapse_repeated_occurrence','source_sha256':hashlib.sha256(mutant.encode()).hexdigest(),'status':'REJECTED','returncode':rc,'rejected_by':'finite_examples'})
    (project/'E3FiniteExamples.lean').write_text(examples)
    compile_module('E3FiniteExamples','restore_checked_examples')
    after={str(p.relative_to(ROOT)):sha(p) for p in paths}
    require(before==after and sha(ROOT/'source_freeze.json')==freeze_hash,'source changed during run')
    require({str(p.relative_to(ROOT)):sha(p) for p in input_paths()}==before,'source file set changed during run')
    result={'status':'PASS','schema':'e3-formal-receipt-v1','mode':actual_mode,'started_utc':started,'finished_utc':utc(),'elapsed_seconds':round(time.monotonic()-t0,3),'scope':'Checked original C1/A/B and E1 plus new finite graph-groupoid core Cell/Signature/Tree instance; generic semantic equipment/comparison proofs remain P.','source_only':True,'public_upstream_cache_only':True,'inherited_project_oleans':inherited,'run_directory':str(run),'compiler':compiler,'compiler_sha256':sha(args.toolchain/'bin/lean'),'upstream_dependency_pins':pins,'source_freeze_sha256':freeze_hash,'source_sha256_before':before,'source_sha256_after':after,'copied_original_source_hashes':originals,'stages':stages,'axiom_closures':closures,'semantic_mutations':mresults}
    output.parent.mkdir(parents=True,exist_ok=True)
    fd,tmp=tempfile.mkstemp(prefix='.receipt_',dir=output.parent)
    try:
        with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
        guard_output(output,paths);os.replace(tmp,output)
    finally:
        if os.path.exists(tmp):os.unlink(tmp)
    print(json.dumps({'status':'PASS','mode':actual_mode,'axiom_closures':len(closures),'semantic_mutations':len(mresults),'receipt':str(output),'receipt_sha256':sha(output)},sort_keys=True))
    return 0
if __name__=='__main__':
    try:sys.exit(main())
    except (RuntimeError,OSError,ValueError,KeyError,argparse.ArgumentError,subprocess.SubprocessError) as e:sys.exit(reject(str(e)))
