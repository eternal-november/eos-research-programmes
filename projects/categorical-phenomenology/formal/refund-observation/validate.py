#!/usr/bin/env python3
"""Fresh Lean build, exact dependency copies, theorem-type audit, negative controls."""
import hashlib, json, os, re, shutil, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parent
lean_bin = os.environ.get('LEAN_BIN') or shutil.which('lean')
if not lean_bin:
    raise SystemExit('Lean not found. Install Lean 4.35.0, then set LEAN_BIN to its binary or put lean on PATH.')
LEAN = Path(lean_bin).expanduser().resolve()
DEPENDENCY_HASHES = {
    'ResourceObservation.lean': '2bce2dd651117adf12e29edf967f91422cf0aea422549552063ec4a1e8f1e57a',
    'ResourceObservationIff.lean': 'b607a2ee5b7a2420d52acdb0022cdc491654b353a9d9e4127d7dcad4513df08b',
}
BUILD = ROOT / '.build'
if BUILD.exists():
    shutil.rmtree(BUILD)
BUILD.mkdir()
ENV = dict(os.environ, LEAN_PATH=str(BUILD))
version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
if 'version 4.35.0,' not in version:
    raise SystemExit('This package is pinned to Lean 4.35.0. Found: ' + version)
results = {'lean': version,
           'positive': [], 'negative': [], 'dependency_copies': {}}
for name in ('ResourceObservation.lean', 'ResourceObservationIff.lean'):
    copied = ROOT / 'dependencies' / name
    digest = hashlib.sha256(copied.read_bytes()).hexdigest()
    assert digest == DEPENDENCY_HASHES[name], 'Dependency hash mismatch: ' + name
    results['dependency_copies'][name] = digest

sources = [ROOT / 'dependencies/ResourceObservation.lean',
           ROOT / 'dependencies/ResourceObservationIff.lean',
           ROOT / 'OrderedGroupRefunds.lean', ROOT / 'BoundedRefunds.lean',
           ROOT / 'ClassicalGroupCorollary.lean', ROOT / 'PreorderControl.lean',
           ROOT / 'AuditSignatures.lean']
for source in sources:
    body = source.read_text()
    # No command-level axiom declaration or sorry/admit proof placeholder.
    assert not re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit)\b', body, re.M), source
    command = [str(LEAN), '-o', str((BUILD / (source.stem + '.olean')).relative_to(ROOT)), str(source.relative_to(ROOT))]
    p = subprocess.run(command, env=ENV, cwd=ROOT, text=True, capture_output=True)
    output = p.stdout + p.stderr
    (ROOT / (source.name + '.log')).write_text(output)
    assert p.returncode == 0 and 'sorryAx' not in output, (source, output)
    results['positive'].append({'file': str(source.relative_to(ROOT)), 'exit_code': p.returncode,
                                'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})

# These deliberately broken programs must fail. The first removes the key
# factor-bound transport; the second changes a shifted threshold sign.
mutations = [
    ('drop_factor_transport.lean', (ROOT/'OrderedGroupRefunds.lean').read_text().replace(
        'g.trans (g.mono (g.refl a) hyc) hac', 'g.trans (g.refl _) hac')),
    ('wrong_left_threshold.lean', (ROOT/'BoundedRefunds.lean').read_text().replace(
        '(coverA : ∀ a, IntWindow l (C-r) a → A a)',
        '(coverA : ∀ a, IntWindow l (C+r) a → A a)', 1)),
    ('invalid_naive_cap.lean', '''import BoundedRefunds
open ResourceObservation
example : BoundedUniversalAgreement (-2) 1 3 (IntWindow (-2) 3) (IntWindow 1 3) :=
  shifted_windows_suffice (-2) 1 3
''')]
for name, body in mutations:
    source = ROOT / 'negative_tests' / name
    source.write_text(body)
    p = subprocess.run([str(LEAN), str(source.relative_to(ROOT))], env=ENV, cwd=ROOT, text=True, capture_output=True)
    output = p.stdout + p.stderr
    source.with_suffix('.lean.log').write_text(output)
    assert p.returncode != 0 and 'error' in output, (name, 'unexpectedly accepted')
    results['negative'].append({'file': 'negative_tests/'+name,
                                'exit_code': p.returncode, 'expected_failure': True})

# Exact axiom fingerprints, extracted from the successfully built modules.
axioms = {}
for source in sources:
    output = (ROOT / (source.name + '.log')).read_text()
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        axioms[name] = []
    for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        axioms[name] = [re.sub(r'\.\{[^}]*\}', '', x.strip()) for x in deps.split(',')]
assert axioms['ResourceObservation.OrderedAbelianGroupData.universal_agreement_iff_nonempty_forces_all'] == []
assert axioms['ResourceObservation.OrderedAbelianGroupData.universal_agreement_iff_empty_or_all_decidable'] == []
assert set(axioms['ResourceObservation.integer_refund_counterexample']) == {'propext'}
assert set(axioms['ResourceObservation.bounded_universal_agreement_iff_coverage']) == {'propext', 'Quot.sound'}
assert all('sorryAx' not in v for v in axioms.values())
results['axioms'] = axioms
results['all_passed'] = True
(ROOT / 'validation.json').write_text(json.dumps(results, indent=2)+'\n')
print(json.dumps(results, indent=2))
