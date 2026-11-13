#!/usr/bin/env python3
"""Independent fresh-project audit. Never edits mathematical source or historical manifests."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, subprocess, sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
STANDARD_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def source_paths():
    paths = list((ROOT / 'WitnessedDecompositions').rglob('*.lean'))
    paths += list(ROOT.glob('*.lean'))
    paths += list(HERE.glob('*.lean'))
    paths += list((HERE / 'negative').glob('*.lean.fail'))
    paths += [ROOT / x for x in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]
    paths += [HERE / 'BASELINE_HASHES.json', Path(__file__).resolve()]
    return sorted(set(paths))

def snapshot():
    return {str(p.relative_to(ROOT)): sha(p) for p in source_paths()}

def check_baseline():
    data = json.loads((HERE / 'BASELINE_HASHES.json').read_text())
    for name, expected in data['sha256'].items():
        if sha(ROOT / name) != expected:
            raise RuntimeError(f'Original source or historical manifest changed: {name}')
    return len(data['sha256'])

def lean_code(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: i += 1
        elif text.startswith('/-', i): depth = 1; i += 2
        elif text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            out.append(' ')
        else: out.append(text[i]); i += 1
    if depth: raise RuntimeError('Unterminated Lean comment in source screen')
    return ''.join(out)

def source_screen():
    checked = []
    for p in source_paths():
        if p.suffix != '.lean': continue
        code = lean_code(p.read_text())
        hit = re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide)\b', code)
        if hit:
            raise RuntimeError(f'Forbidden proof token {hit.group()} in {p.relative_to(ROOT)}')
        checked.append(str(p.relative_to(ROOT)))
    return checked

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record-freeze', action='store_true')
    parser.add_argument('--work', type=Path)
    args = parser.parse_args()
    baseline_count = check_baseline()
    screened = source_screen()
    freeze_file = HERE / 'SOURCE_FREEZE.json'
    frozen = snapshot()
    if args.record_freeze:
        freeze_file.write_text(json.dumps({'sha256': frozen}, indent=2) + '\n')
        print('Recorded', len(frozen), 'frozen source/configuration files; baseline entries:', baseline_count)
        return
    if not freeze_file.exists(): raise RuntimeError('Record source freeze after lead declares stable')
    expected = json.loads(freeze_file.read_text())['sha256']
    if frozen != expected: raise RuntimeError('Source no longer matches independent freeze')
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = (args.work or ROOT.parent / ('independent_fresh_' + stamp)).resolve()
    if work.exists(): raise RuntimeError(f'Refusing to reuse existing audit work directory: {work}')
    work.mkdir(parents=True)
    evidence = HERE / 'evidence' / stamp
    evidence.mkdir(parents=True)
    for rel in expected:
        source = ROOT / rel; target = work / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    (work / '.lake').mkdir()
    (work / '.lake' / 'packages').symlink_to(ROOT / '.lake' / 'packages', target_is_directory=True)
    if (work / '.lake' / 'build').exists(): raise RuntimeError('Fresh project unexpectedly has local build artifacts')
    commands = []
    def run(cmd, label, expected_failure=False):
        process = subprocess.run(cmd, cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (evidence / (label + '.log')).write_text(process.stdout)
        commands.append({'command':cmd, 'label':label, 'exit':process.returncode, 'expected_failure':expected_failure})
        print(label, 'exit', process.returncode, flush=True)
        if expected_failure:
            if process.returncode == 0: raise RuntimeError('Negative control unexpectedly compiled: ' + label)
            if re.search(r'unknown module|object file.*does not exist|cannot find|no such file', process.stdout, re.I):
                raise RuntimeError('Negative control failed due to missing infrastructure: ' + label)
            if 'error:' not in process.stdout and 'error(' not in process.stdout:
                raise RuntimeError('Negative control failed without Lean type error: ' + label)
        elif process.returncode:
            raise RuntimeError('Command failed: ' + label + '\n' + process.stdout[-10000:])
        return process.stdout
    version = run(['lean','--version'], 'lean-version')
    if not re.search(r'\bversion 4\.35\.0\b', version): raise RuntimeError('Unexpected Lean version')
    run(['lake','--version'], 'lake-version')
    modules = sorted(p.stem for p in (work/'WitnessedDecompositions'/'Dynamic').glob('*.lean'))
    run(['lake','build'] + ['WitnessedDecompositions.Dynamic.' + name for name in modules], 'dynamic-fresh-build')
    # Explicitly compile each independent fixture to fresh project output; tests may import earlier fixtures.
    fixtures = ['OriginalOccurrenceRegressions', 'TupleRegressions', 'TargetRegressions', 'BridgeRegressions']
    out = work / '.lake' / 'build' / 'lib' / 'lean' / 'audit' / 'dynamic_independent'
    out.mkdir(parents=True, exist_ok=True)
    for name in fixtures:
        source = Path('audit/dynamic_independent') / (name + '.lean')
        if not (work/source).exists(): raise RuntimeError('Missing required independent fixture: ' + str(source))
        run(['lake','env','lean','-R','.', '-o',str(out/(name+'.olean')),str(source)], name)
    for negative in sorted((work/'audit'/'dynamic_independent'/'negative').glob('*.lean.fail')):
        runnable = negative.with_suffix('')
        shutil.copyfile(negative, runnable)
        run(['lake','env','lean',str(runnable.relative_to(work))], 'negative-' + negative.name, True)
    axiom_source = Path('audit/dynamic_independent/HeadlineAxioms.lean')
    text = run(['lake','env','lean',str(axiom_source)], 'headline-axioms')
    n = len(re.findall(r'^\s*#print\s+axioms\b', (work/axiom_source).read_text(), re.M))
    closures = re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, re.S)
    empty = len(re.findall(r'does not depend on any axioms', text))
    if n != len(closures) + empty: raise RuntimeError('Axiom closure report count mismatch')
    seen = {a.strip() for c in closures for a in c.split(',') if a.strip()}
    if seen - STANDARD_AXIOMS: raise RuntimeError('Unexpected theorem axioms: ' + str(sorted(seen-STANDARD_AXIOMS)))
    check_baseline()
    if snapshot() != expected: raise RuntimeError('Original frozen source changed during audit')
    for rel,digest in expected.items():
        if sha(work/rel) != digest: raise RuntimeError('Fresh copied source changed: ' + rel)
    report = {'status':'PASS','fresh_workcopy':str(work),'evidence_directory':str(evidence),
      'commands':commands,'baseline_entries_unchanged':baseline_count,
      'screened_lean_files':screened,'axiom_reports':n,'axiom_union':sorted(seen),
      'source_sha256':expected,
      'dependency_trust':'Pinned official Lean 4.35.0; upstream mathlib compiled cache shared. No project .olean files reused.',
      'scope':'Focused actual dynamic target Calc, graph/tuple/nullary semantics, original extension/refinement API, independent discriminating examples. Not full paper formalization.'}
    (evidence/'RESULT.json').write_text(json.dumps(report,indent=2)+'\n')
    (HERE/'LATEST_RESULT.json').write_text(json.dumps({'result':str(evidence/'RESULT.json')},indent=2)+'\n')
    print('PASS:', evidence/'RESULT.json')

if __name__ == '__main__':
    try: main()
    except Exception as exc:
        print('INDEPENDENT AUDIT FAILED:',exc,file=sys.stderr)
        sys.exit(1)
