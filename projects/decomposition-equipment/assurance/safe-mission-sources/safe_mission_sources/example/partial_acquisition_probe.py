#!/usr/bin/env python3
"""Frozen partial-acquisition relational diagnostic; not a robot mission result."""
from __future__ import annotations
import hashlib
import itertools
import json
from pathlib import Path
import random
import time
from relational_engine import Catalogue, ForestKnowledge, iter_ids

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def advance(counters, command, L):
    return tuple(min(L, x + 1) if a else 0 for x, a in zip(counters, command))


def plant_bit(mechanism, counters):
    # Independent scalar generator/scorer. Never consulted by a proof query.
    bits = [int(counters[p] >= r) for p, r in mechanism['features']]
    return (mechanism['table'] >> (bits[0] + 2*bits[1])) & 1


def essential_tables():
    return [t for t in range(16) if
            any(((t >> x) & 1) != ((t >> (x ^ 1)) & 1) for x in range(4)) and
            any(((t >> x) & 1) != ((t >> (x ^ 2)) & 1) for x in range(4))]


def interface_summary(k, i):
    cat = k.catalogue
    domain = k.domains[i]
    scopes, thresholds, tables = set(), set(), set()
    for h in iter_ids(domain):
        d = cat.describe(h)
        scopes.add(tuple(p for p, r in d['features']))
        thresholds.add(tuple(tuple(f) for f in d['features']))
        tables.add((d['arity'], d['table']))
    return {'candidate_functions': domain.bit_count(),
            'distinct_essential_scopes': len(scopes),
            'distinct_scope_threshold_assignments': len(thresholds),
            'distinct_arity_tables': len(tables),
            'scope_alternatives': [list(s) for s in sorted(scopes)]}


def assess(k, edge, current, future_contexts):
    """Check each possible coordinate branch, then pick one uniform tail guard."""
    i, j = edge
    branches = []
    outcomes = k.possible_coordinate(i, current)
    for bit in outcomes:
        branch = k.copy()
        assert branch.observe_coordinate(i, current, bit)
        eligible = [u for u in edge if branch.guarantees([(u, c, 1) for c in future_contexts])]
        branches.append({'coordinate_outcome': bit, 'certified_endpoints': eligible,
                         'chosen_endpoint': eligible[0] if eligible else None,
                         'endpoint_interfaces_after_diagnostic':
                             {str(u): interface_summary(branch, u) for u in edge}})
    return {'guaranteed_choice_for_every_branch': bool(outcomes) and all(
                b['certified_endpoints'] for b in branches),
            'branches': branches}


def main():
    config_path = ROOT/'partial_acquisition_config.json'
    cfg = json.loads(config_path.read_text())
    assert cfg['frozen_before_outcomes']
    assert len(cfg['initial_command_vectors']) == 12
    assert all(sum(p) <= 2 for p in cfg['initial_command_vectors'] + cfg['held_patterns'])
    started = time.perf_counter()
    cat = Catalogue(cfg['n_ports'], cfg['L'])
    tables = essential_tables()
    assert len(tables) == 10
    runs = []
    counts = {'trials': 0, 'exact_success': 0, 'rectangular_success': 0,
              'exact_only_success': 0, 'rectangular_only_success': 0,
              'neither_success': 0, 'actual_truth_tail_violations': 0,
              'exact_only_with_changing_future_context': 0,
              'exact_only_with_more_than_two_functions_in_an_endpoint': 0,
              'exact_only_with_scope_ambiguity_in_an_endpoint': 0,
              'exact_only_with_threshold_ambiguity_beyond_scope': 0,
              'exact_only_with_more_than_two_arity_tables_in_an_endpoint': 0}
    by_seed = []
    for seed in cfg['truth_seeds']:
        rng = random.Random(seed)
        truth = []
        for i in range(cfg['n_outputs']):
            ports = sorted(rng.sample(range(cfg['n_ports']), 2))
            truth.append({'features': [[p, rng.randint(2, cfg['L'])] for p in ports],
                          'table': rng.choice(tables)})
        truth_ids = [cat.find(m['features'], m['table']) for m in truth]
        k = ForestKnowledge(cat, cfg['n_outputs'])
        # Actual explicitly charged all-off initialization, not injected history.
        c = (cfg['L'],) * cfg['n_ports']  # unknown earlier positive history is flushed
        flush_records = []
        for tick in range(cfg['initial_flush_ticks']):
            c = advance(c, cfg['initial_flush_command'], cfg['L'])
            flush_records.append({'tick': tick, 'command': cfg['initial_flush_command'],
                                  'counters_after': list(c)})
        assert c == (0,) * cfg['n_ports']
        records = []
        for tick, command in enumerate(cfg['initial_command_vectors']):
            c = advance(c, command, cfg['L'])
            edge = cfg['edges'][tick % len(cfg['edges'])]
            total = sum(plant_bit(truth[u], c) for u in edge)
            assert k.observe_sum(*edge, c, total)
            assert all((k.domains[i] >> h) & 1 for i, h in enumerate(truth_ids))
            records.append({'tick_after_flush': tick + 1, 'command': command,
                            'counters_after': list(c), 'observed_edge': edge,
                            'observed_sum': total})
        base_c = c
        trials = []
        seed_count = {'seed': seed, 'trials': 0, 'exact_success': 0,
                      'rectangular_success': 0, 'exact_only_success': 0}
        for command, prep, edge in itertools.product(cfg['held_patterns'], cfg['prep_lengths'], cfg['edges']):
            c = base_c
            prep_records = []
            for tick in range(prep):
                c = advance(c, command, cfg['L'])
                prep_records.append(list(c))
            exact = k.copy()
            total = sum(plant_bit(truth[u], c) for u in edge)
            assert exact.observe_sum(*edge, c, total)
            assert exact.feasible(domain_restrictions={i: 1 << h for i, h in enumerate(truth_ids)})
            rectangular = ForestKnowledge(cat, cfg['n_outputs'])
            rectangular.domains = list(exact.domains)  # exact local projections, relations deliberately discarded
            assert rectangular.consistent()
            tail, future = c, []
            for tick in range(cfg['diagnostic_horizon_ticks']):
                tail = advance(tail, command, cfg['L'])
                future.append(tail)
            unique_future = list(dict.fromkeys(future))
            ex = assess(exact, edge, c, unique_future)
            rect = assess(rectangular, edge, c, unique_future)
            a = ex['guaranteed_choice_for_every_branch']
            b = rect['guaranteed_choice_for_every_branch']
            # Knowledge inclusion requires rectangular success => exact success.
            assert not b or a
            actual_bit = plant_bit(truth[edge[0]], c)
            actual_branch = next(br for br in ex['branches'] if br['coordinate_outcome'] == actual_bit)
            actual_violation = False
            if actual_branch['chosen_endpoint'] is not None:
                u = actual_branch['chosen_endpoint']
                actual_violation = any(plant_bit(truth[u], x) != 1 for x in future)
                assert not actual_violation
            iface = {str(u): interface_summary(exact, u) for u in edge}
            changing = any(x != c for x in unique_future)
            only = a and not b
            counts['trials'] += 1
            counts['exact_success'] += a
            counts['rectangular_success'] += b
            counts['exact_only_success'] += only
            counts['rectangular_only_success'] += b and not a
            counts['neither_success'] += not a and not b
            counts['actual_truth_tail_violations'] += actual_violation
            counts['exact_only_with_changing_future_context'] += only and changing
            counts['exact_only_with_more_than_two_functions_in_an_endpoint'] += only and any(
                x['candidate_functions'] > 2 for x in iface.values())
            counts['exact_only_with_scope_ambiguity_in_an_endpoint'] += only and any(
                x['distinct_essential_scopes'] > 1 for x in iface.values())
            counts['exact_only_with_threshold_ambiguity_beyond_scope'] += only and any(
                x['distinct_scope_threshold_assignments'] > x['distinct_essential_scopes'] for x in iface.values())
            counts['exact_only_with_more_than_two_arity_tables_in_an_endpoint'] += only and any(
                x['distinct_arity_tables'] > 2 for x in iface.values())
            for key, value in [('trials',1),('exact_success',a),('rectangular_success',b),('exact_only_success',only)]:
                seed_count[key] += int(value)
            trials.append({'held_command': command, 'prep_ticks': prep, 'edge': edge,
                           'prep_counter_trace': prep_records, 'diagnostic_context': list(c),
                           'observed_sum': total, 'future_ticks': len(future),
                           'unique_future_contexts': [list(x) for x in unique_future],
                           'counter_context_changes_during_tail': changing,
                           'endpoint_interfaces_before_coordinate': iface,
                           'exact': ex, 'rectangular': rect,
                           'actual_coordinate_outcome': actual_bit,
                           'actual_selected_tail_violation': actual_violation})
        runs.append({'seed': seed, 'truth_for_generator_and_scoring_only': truth,
                     'flush_trace': flush_records, 'base_acquisition_records': records,
                     'base_counter_context': list(base_c), 'base_knowledge_metrics': k.metrics(),
                     'trials': trials})
        by_seed.append(seed_count)
    output = {'config_sha256': digest(config_path), 'source_sha256': digest(__file__),
              'engine_sha256': digest(ROOT/'relational_engine.py'),
              'frozen_config': cfg, 'counts': counts, 'by_seed': by_seed,
              'elapsed_seconds': time.perf_counter() - started,
              'interpretation': 'Exact universal model-side diagnostic under declared deterministic function class; no physical bay accessibility, motion, resource or mission claim. All99trial situations per seed are separate continuations of same base record, not one sequential execution.',
              'runs': runs}
    (ROOT/'partial_acquisition_results.json').write_text(json.dumps(output, indent=2) + '\n')
    summary = {k:v for k,v in output.items() if k not in ('runs','frozen_config')}
    (ROOT/'partial_acquisition_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
