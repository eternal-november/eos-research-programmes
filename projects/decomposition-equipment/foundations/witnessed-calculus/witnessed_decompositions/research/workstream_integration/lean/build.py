#!/usr/bin/env python3
"""Fresh modules; explicit portable dependency/toolchain selection, no old project oleans."""
from pathlib import Path
import os, subprocess, json, datetime, hashlib, re, sys, importlib.util, shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
RECOVERY = Path('/workspace/shared/witnessed_B_20261024/toolchain_recovery')
now = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
OUT = HERE / 'runs' / now
BUILD = OUT / 'fresh'
BUILD.mkdir(parents=True)
new = ['QuotientArrowCertificates', 'GraphForestNormalForms', 'PublicExampleBridge']
seen, order = set(), []


def visit(name):
    if name in seen:
        return
    seen.add(name)
    if name.startswith('WitnessedDecompositions.'):
        source = ROOT / Path(*name.split('.')).with_suffix('.lean')
        scope = ROOT
    elif name in ['GraphCoordinates', 'TypedNormalizerAlgebra', 'RewriteFragmentCandidate']:
        source = ROOT / 'research/workstream_A/rewrite' / f'{name}.lean'
        scope = source.parent
    elif name in new or name == 'AxiomAudit':
        source, scope = HERE / f'{name}.lean', HERE
    else:
        return
    for dep in re.findall(r'^(?:public )?import ([\w.]+)', source.read_text(), re.M):
        visit(dep)
    order.append((name, source, scope))


for n in new:
    visit(n)
visit('AxiomAudit')
spec = importlib.util.spec_from_file_location('inherited_screen', ROOT / 'scripts/verify_export.py')
screen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(screen)


def verify_baseline():
    record = json.loads((ROOT / 'research/workstream_integration/BaselinePreservation.json').read_text())
    for item in record['files']:
        assert hashlib.sha256((ROOT / item['path']).read_bytes()).hexdigest() == item['sha256'], item['path']
    return len(record['files'])


def configure_environment():
    """Prefer this checkout; an external project/cache must be explicitly selected."""
    env = dict(os.environ)
    recovery = env.get('WITNESSED_USE_RECOVERY') == '1'
    tool_value = env.get('WITNESSED_TOOLCHAIN_ROOT')
    tool = Path(tool_value).expanduser().resolve() if tool_value else (RECOVERY if recovery else None)
    if tool is not None:
        bins = [tool / 'bin', tool / 'lean-4.35.0-linux/bin']
        binary = next((p for p in bins if (p / 'lean').is_file() and (p / 'lake').is_file()), None)
        if binary is None:
            raise RuntimeError(f'No lean/lake pair under explicit toolchain root: {tool}')
        env['PATH'] = str(binary) + os.pathsep + env.get('PATH', '')
        if recovery and (tool / 'cache').is_dir():
            env.setdefault('XDG_CACHE_HOME', str(tool / 'cache'))
    if not shutil.which('lean', path=env.get('PATH')) or not shutil.which('lake', path=env.get('PATH')):
        raise RuntimeError('Install Lean 4.35.0 on PATH or set WITNESSED_TOOLCHAIN_ROOT. '
                           'The historical recovery toolchain requires explicit WITNESSED_USE_RECOVERY=1.')
    source_lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    own_packages = ROOT / source_lock.get('packagesDir', '.lake/packages')
    override = env.get('WITNESSED_LAKE_PROJECT')
    if override:
        project, mode = Path(override).expanduser().resolve(), 'explicit_lake_project'
    elif own_packages.is_dir():
        project, mode = ROOT, 'current_source_checkout'
    elif recovery:
        project, mode = RECOVERY / 'baseline', 'explicit_historical_recovery'
    else:
        raise RuntimeError('This checkout has no installed Lake packages. Install its pinned dependencies '
                           'or set WITNESSED_LAKE_PROJECT to a project with the same locked revisions. '
                           'Historical fallback is opt-in: WITNESSED_USE_RECOVERY=1.')
    selected_lock = json.loads((project / 'lake-manifest.json').read_text())
    wanted = {p['name']: p.get('rev') for p in source_lock['packages']}
    selected = {p['name']: p.get('rev') for p in selected_lock['packages']}
    if any(selected.get(name) != rev for name, rev in wanted.items()):
        raise RuntimeError('Selected Lake project does not match every delivered dependency revision.')
    version = subprocess.check_output(['lean', '--version'], env=env, text=True).strip()
    if not re.search(r'\bversion 4\.35\.0\b', version):
        raise RuntimeError('Wrong Lean version: ' + version)
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], env=env, text=True).strip())
    standard = (prefix / 'lib/lean').resolve()
    packages = (project / selected_lock.get('packagesDir', '.lake/packages')).resolve()
    project_build = (project / '.lake/build').resolve()
    git_records = {}
    git_env = dict(env, GIT_OPTIONAL_LOCKS='0')
    for name, rev in wanted.items():
        package = (packages / name).resolve()
        git = shutil.which('git', path=env.get('PATH'))
        top = subprocess.run([git, '-C', str(package), 'rev-parse', '--show-toplevel'],
                             env=git_env, text=True, capture_output=True) if git else None
        if top is None or top.returncode or Path(top.stdout.strip()).resolve() != package:
            git_records[name] = {'path': str(package), 'expected_rev': rev,
                                 'status': 'GIT_METADATA_UNAVAILABLE_LOCK_ONLY'}
            continue
        head = subprocess.check_output([git, '-C', str(package), 'rev-parse', '--verify', 'HEAD'],
                                       env=git_env, text=True).strip()
        if head != rev:
            raise RuntimeError(f'Actual dependency Git HEAD mismatch for {name}: {head} != {rev}')
        dirty = subprocess.run([git, '-C', str(package), 'diff', '--no-ext-diff', '--quiet',
                                'HEAD', '--'], env=git_env, text=True, capture_output=True)
        if dirty.returncode != 0:
            raise RuntimeError(f'Tracked dependency worktree differs from pinned HEAD: {name}')
        git_records[name] = {'path': str(package), 'expected_rev': rev, 'actual_head': head,
                             'status': 'HEAD_MATCH_TRACKED_WORKTREE_CLEAN'}
    raw = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=project, env=env,
                         text=True, capture_output=True, check=True).stdout.strip()
    external, rejected = [], []
    for item in raw.split(os.pathsep):
        if not item:
            continue
        p = Path(item)
        p = p.resolve() if p.is_absolute() else (project / p).resolve()
        # Only selected package trees and compiler stdlib survive. In particular,
        # the selected project's .lake/build/lib/lean is NEVER admitted.
        if not p.is_relative_to(project_build) and (p.is_relative_to(packages) or p == standard):
            external.append(str(p))
        else:
            rejected.append(str(p))
    if not any(Path(p).is_relative_to(packages) for p in external):
        raise RuntimeError('No supported package dependency paths found in selected Lake environment.')
    env['LEAN_PATH'] = os.pathsep.join([str(BUILD)] + external)
    return env, {'dependency_selection': mode, 'lake_project': str(project),
                 'toolchain_root_override': str(tool) if tool else None,
                 'recovery_explicitly_enabled': recovery, 'lean_version': version,
                 'external_lean_path': external, 'rejected_project_lean_paths': rejected,
                 'matched_dependency_revisions': wanted,
                 'canonical_package_root': str(packages),
                 'canonical_project_build_excluded': str(project_build),
                 'package_git_checks': git_records,
                 'external_cache_trust': 'Git HEAD and tracked-worktree checks are source provenance, not a rebuild or cryptographic verification of generated external oleans; packages without Git metadata are explicitly lock-only.'}


result = {'status': 'RUNNING', 'out': str(OUT), 'modules': []}
try:
    result['baseline_before'] = verify_baseline()
    env, configuration = configure_environment()
    result.update(configuration)
    for n in new + ['AxiomAudit']:
        code = screen.lean_code((HERE / (n + '.lean')).read_text())
        if re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom|implemented_by)\b', code):
            raise RuntimeError('Forbidden theorem source command: ' + n)
    for name, source, scope in order:
        target = BUILD / Path(*name.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        cmd = ['lean', '-R', str(scope), '-o', str(target), str(source)]
        run = subprocess.run(cmd, cwd=ROOT, env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = OUT / (name.replace('.', '_') + '.log')
        log.write_text(run.stdout)
        result['modules'].append({'module': name, 'source': str(source.relative_to(ROOT)),
                                  'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                                  'exit': run.returncode})
        print(name, run.returncode, flush=True)
        if run.returncode:
            print(run.stdout, flush=True)
            raise RuntimeError(name + ' failed')
        if name == 'AxiomAudit':
            screen.audit_axioms(str(source.relative_to(ROOT)), log, screen.STANDARD)
            result['axiom_report_count'] = len(re.findall(r'^#print axioms', source.read_text(), re.M))
    result['baseline_after'] = verify_baseline()
    result['status'] = 'PASS'
except BaseException as exc:
    result.update(status='FAIL', error=repr(exc))
    print(repr(exc), flush=True)
finally:
    result['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (OUT / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(str(OUT), flush=True)
sys.exit(0 if result['status'] == 'PASS' else 1)
