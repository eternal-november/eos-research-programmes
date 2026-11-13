#!/usr/bin/env python3
"""Source-only E1 rebuild; reuse only pinned public upstream dependency objects.
No download, lake update, inherited project .olean, or optimization-sensitive assert.
"""
import argparse, datetime, hashlib, json, os, pathlib, re, shutil, subprocess, tempfile, time
ROOT = pathlib.Path(__file__).resolve().parent
DEFAULT = pathlib.Path('/workspace/shared/d1_equivariant_transport_20261031/formal/toolchain')

def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def require(test, msg):
    if not test: raise RuntimeError(msg)
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--toolchain', type=pathlib.Path, default=DEFAULT/'lean-4.35.0-linux')
    ap.add_argument('--upstream-project', type=pathlib.Path, default=DEFAULT/'project')
    ap.add_argument('--output', type=pathlib.Path, default=ROOT/'fresh_result.json')
    ap.add_argument('--work-parent', type=pathlib.Path, default=ROOT)
    args = ap.parse_args()
    t0=time.monotonic(); started=utc()
    paths = [ROOT/'E1RelationEquipment.lean', ROOT/'E1FiniteExamples.lean', ROOT/'setup_fresh.sh', ROOT/'verify_fresh.py', ROOT/'README_FORMAL.md']
    paths += sorted(p for p in (ROOT/'original_source').rglob('*') if p.is_file())
    before={str(p.relative_to(ROOT)):sha(p) for p in paths}
    require(not any(p.suffix in ('.olean','.ilean','.ir') for p in paths), 'Bundled original input is not source-only')
    lock=json.loads((ROOT/'original_source/lake-manifest.json').read_text())
    require(sha(ROOT/'original_source/lake-manifest.json')=='0e4afebb985207e83e2a2fdf3d42281f9986e939ebc31084eaa5f8c3479c22cc', 'Original dependency lock changed')
    require((ROOT/'original_source/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.35.0', 'Toolchain pin changed')
    env=dict(os.environ); env['PATH']=str(args.toolchain.resolve()/'bin')+os.pathsep+env['PATH']
    env['E1_UPSTREAM_PROJECT']=str(args.upstream_project.resolve())
    env['E1_ORIGINAL_SOURCE']=str(ROOT/'original_source')
    env.pop('LEAN_PATH', None)
    compiler=subprocess.check_output([str(args.toolchain/'bin/lean'),'--version'],text=True,env=env).strip()
    require('version 4.35.0' in compiler and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in compiler, 'Compiler version/commit mismatch')
    pins=[]
    for dep in lock['packages']:
        d=args.upstream_project/'.lake/packages'/dep['name']
        rev=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()
        require(rev==dep['rev'], f"Wrong upstream pin {dep['name']}")
        clean=subprocess.run(['git','-C',str(d),'diff','--quiet','HEAD','--']).returncode == 0
        require(clean, f"Tracked upstream source modified: {dep['name']}")
        pins.append({'name':dep['name'],'expected':dep['rev'],'actual':rev,'tracked_source_clean':clean})
    run=pathlib.Path(tempfile.mkdtemp(prefix='fresh_e1_',dir=args.work_parent)); project=run/'project'
    subprocess.run(['bash',str(ROOT/'setup_fresh.sh'),str(project)],env=env,check=True)
    for name in ('E1RelationEquipment.lean','E1FiniteExamples.lean'): shutil.copy2(ROOT/name,project/name)
    # Do not follow dependency symlinks: all non-upstream object files must be absent.
    inherited=[str(p.relative_to(project)) for p in project.rglob('*.olean') if '.lake/packages/' not in str(p)]
    require(not inherited,'Inherited project objects detected')
    originals={str(p.relative_to(ROOT/'original_source')):sha(p) for p in (ROOT/'original_source').rglob('*') if p.is_file()}
    require(all(sha(project/rel)==h for rel,h in originals.items()),'Original source copy differs')
    stages=[]
    def run_stage(name, cmd, expect_success=True):
        logfile=run/(name+'.log')
        with logfile.open('w') as f: cp=subprocess.run(cmd,cwd=project,env=env,stdout=f,stderr=subprocess.STDOUT)
        content=logfile.read_text()
        if expect_success:
            require(cp.returncode==0,f'{name} failed; see {logfile}')
            require('sorryAx' not in content and 'declaration uses `sorry`' not in content,f'{name} has proof holes')
        stages.append({'name':name,'command':cmd,'returncode':cp.returncode,'log':str(logfile),'log_sha256':sha(logfile)})
        return cp.returncode,content
    original_targets=['WitnessedDecompositions'] + ['WitnessedDecompositions.'+p.stem for p in sorted((ROOT/'original_source/WitnessedDecompositions').glob('*.lean'))]
    run_stage('original_build',['lake','build']+original_targets)
    c2='research/workstream_C2/lean/RelationInterface'
    (project/'.lake/build/lib/lean/research/workstream_C2/lean').mkdir(parents=True,exist_ok=True)
    run_stage('original_relation',['lake','env','lean','-o',f'.lake/build/lib/lean/{c2}.olean',f'{c2}.lean'])
    closures={}
    for name in ('E1RelationEquipment','E1FiniteExamples'):
        _,out=run_stage(name,['lake','env','lean','-o',f'.lake/build/lib/lean/{name}.olean',name+'.lean'])
        require('warning:' not in out, f'{name}: warning in final build')
        for line in out.splitlines():
            m=re.match(r"'([^']+)' (.*)",line)
            if m:
                ax=[] if 'does not depend on any axioms' in m[2] else re.search(r'\[(.*?)\]',m[2]).group(1).split(', ')
                require(set(ax)<= {'propext','Quot.sound'},f'Unexpected axioms {ax}')
                closures[m[1]]=ax
    require(len(closures)>=45,'Axiom audit unexpectedly incomplete')
    source=(ROOT/'E1RelationEquipment.lean').read_text()
    mutations=[
      ('erase_restriction_scalar','toFun α := ⟨α.weight, α.valid⟩','toFun α := ⟨0, α.valid⟩'),
      ('erase_inner_scalar_sum','a.cell.weight + Path.sum a.profile (fun i => (f i).cell.weight),','a.cell.weight,'),
      ('erase_context_scalar','⟨β.weight + α.weight, fun x y hxy => β.valid x y','⟨β.weight, fun x y hxy => β.valid x y'),
      ('weaken_exact_to_containment','RelationInterface.evaluate a.profile = c.edge ∧ a.cell.weight = 0','RelationInterface.Included (RelationInterface.evaluate a.profile) c.edge ∧ a.cell.weight = 0')]
    mresults=[]
    for name,old,new in mutations:
        require(source.count(old)==1, f'{name}: mutation target not unique')
        target=project/(name+'.lean'); target.write_text(source.replace(old,new,1))
        rc,out=run_stage(name,['lake','env','lean',target.name],expect_success=False)
        require(rc!=0 and 'error:' in out, f'{name}: mutant was not rejected')
        require('unknown module' not in out and 'must be contained in root directory' not in out, f'{name}: infrastructure rejection')
        mresults.append({'name':name,'source_sha256':sha(target),'status':'REJECTED','returncode':rc})
    after={str(p.relative_to(ROOT)):sha(p) for p in paths}
    require(before==after, 'Source changed during run')
    objects={str(p.relative_to(project)):sha(p) for p in project.rglob('*.olean') if '.lake/packages/' not in str(p)}
    result={'status':'PASS','started_utc':started,'finished_utc':utc(),'elapsed_seconds':round(time.monotonic()-t0,3),
      'scope':'Fresh original foundations/C2/B2 + E1 typed fragment + finite Lean examples + four semantic Lean mutations. Python finite tests are separate.',
      'source_only':True,'inherited_project_oleans':inherited,'run_directory':str(run),'compiler':compiler,
      'compiler_sha256':sha(args.toolchain/'bin/lean'),'upstream_dependency_pins':pins,
      'public_upstream_cache_only':True,'source_sha256_before':before,'source_sha256_after':after,
      'copied_original_source_hashes':originals,'stages':stages,'axiom_closures':closures,'semantic_mutations':mresults,'fresh_project_oleans':objects}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    temp=args.output.with_suffix(args.output.suffix+'.tmp'); temp.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n'); os.replace(temp,args.output)
    print(json.dumps({'status':'PASS','axiom_closures':len(closures),'semantic_mutations':len(mresults),'receipt':str(args.output),'receipt_sha256':sha(args.output),'run_directory':str(run)},indent=2))
if __name__=='__main__': main()
