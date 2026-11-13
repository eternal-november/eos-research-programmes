#!/usr/bin/env python3
"""Independent finite public-decoder replay; no general physical-latency claim."""
import ast
import json
import sys
from pathlib import Path
from types import SimpleNamespace
from itertools import combinations, permutations

HERE = Path(__file__).resolve().parent
results = json.loads((HERE / 'observable_enrichment_results.json').read_text())
tree = ast.parse((HERE / 'verify_observable_enrichment.py').read_text())
function = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'decode')
namespace = {'ENV': results['fixed_envelope'], 'ROLES': ('A', 'B', 'A', 'B'),
             'PAIRS': list(combinations(range(4), 2))}
exec(compile(ast.Module(body=[function], type_ignores=[]), 'isolated_decode', 'exec'), namespace)
assert not any(name in namespace for name in ('Plant', 'Learner', 'production', 'pi', 'learner'))
for fixture in results['fixtures']:
    caps = SimpleNamespace(**results['public_caps'])
    output = namespace['decode'](fixture['diagnostic_raw'], fixture['own_request_log'], fixture['batch_raw'], caps)
    assert list(output['y']) == fixture['decoded_y']
    mutated = [[time, 1-bit] for time, bit in fixture['diagnostic_raw']]
    assert namespace['decode'](mutated, fixture['own_request_log'], fixture['batch_raw'], caps) == output
    assert fixture['finished'] == 6812 <= results['fixed_envelope']['deadline']
assert len(results['fixtures']) == 384

# Reproduce the OLD evidence separately; new all-pairs records need not coincide.
sys.path.insert(0, str(HERE / 'observable_reference'))
from reference_shared_pipeline import Plant, Learner, PublicCaps, Budget
old_records = []
for priority in permutations(range(4)):
    if not (priority.index(0) < priority.index(3) and priority.index(1) < priority.index(2)):
        continue
    plant = Plant(priority, payloads=[0]*12, caps=PublicCaps(4, 100, 400, 0))
    learner = Learner(plant, Budget(), plant.caps)
    learner.calibrate()
    assert learner.before(0, 3) and learner.before(1, 2)
    old_records.append((plant.raw, learner.comparisons))
assert len(old_records) == 6 and all(record == old_records[0] for record in old_records)
print('PASS: 384 isolated public-decoder replays; 384 diagnostic-bit mutations; six identical full old evidence records.')

# Same persistent-world supplement: public stage boundaries select the first
# eight singleton records and the six NEW pair stages, retaining old E separately.
supplement = results['same_persistent_world_supplement']
start = supplement['fixed_envelope']['T0']
assert start == 7600 and supplement['fixed_envelope']['deadline'] == 8020
for fixture in supplement['fixtures']:
    raw = fixture['all_diagnostic_raw']
    log = fixture['all_diagnostic_own_request_log']
    assert len(raw) == 24 and len(log) == 16
    assert raw[:12] == fixture['old_raw'] and log[:10] == fixture['old_own_request_log']
    assert fixture['old_end'] == 4318
    decoder_raw, decoder_log = raw[:8] + raw[12:], log[:8] + log[10:]
    output = namespace['decode'](decoder_raw, decoder_log, fixture['batch_raw'],
                                 SimpleNamespace(**results['public_caps']), production_start=start)
    assert output['y'] == (1, 1) and output['b'] == (0, 0, 1, 1)
    assert fixture['finished'] == 8012 <= supplement['fixed_envelope']['deadline']
    mutated = [[time, 1-bit] for time, bit in decoder_raw]
    assert namespace['decode'](mutated, decoder_log, fixture['batch_raw'],
                               SimpleNamespace(**results['public_caps']), production_start=start) == output
assert len(supplement['fixtures']) == 6
assert all(f['old_raw'] == supplement['fixtures'][0]['old_raw'] and
           f['old_own_request_log'] == supplement['fixtures'][0]['old_own_request_log']
           for f in supplement['fixtures'])
print('PASS: six same-persistent-world isolated decoder replays and mutations; old evidence retained; public T0=7600.')
