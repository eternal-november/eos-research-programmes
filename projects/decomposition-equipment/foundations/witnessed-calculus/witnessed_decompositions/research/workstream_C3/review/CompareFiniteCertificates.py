#!/usr/bin/env python3
"""Compare independent finite results with author evidence; no model imports."""
from pathlib import Path
import argparse
import hashlib
import json

def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def matrix_edges(matrix):
    return [[x, y] for x, row in enumerate(matrix) for y, value in enumerate(row) if value]

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--root', type=Path, required=True)
    p.add_argument('--author', type=Path)
    p.add_argument('--independent', type=Path)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    c3 = args.root / 'research/workstream_C3'
    ap = args.author or c3 / 'finite/AuthorCertificate.json'
    ip = args.independent or c3 / 'review/IndependentFinite.json'
    a = json.loads(ap.read_text())
    i = json.loads(ip.read_text())
    assert a['status'] == i['status'] == 'PASS'
    assert a['contract_sha256'] == i['contract_sha256']
    assert a['target_sha256'] == i['target_sha256']
    assert a['source_sha256'] == digest(c3 / 'finite/check_c3.py')
    assert i['source_sha256'] == digest(c3 / 'review/IndependentFinite.py')
    ac, ic = a['graphs']['counts'], i['small_graphs']
    keypairs = [('partition_assignments','partition_assignments'),
                ('graph_partition_pairs','graph_partition_pairs'),
                ('represented_typed_pairs','represented_typed_pairs'),
                ('anchored_fibres','anchored_fibres'),
                ('unanchored_fibres','unanchored_leaf_fibres'),
                ('anchored_inverse_cross_checks','cross_coordinate_inverse_cases')]
    for ak, ik in keypairs:
        assert ac[ak] == ic[ik], (ak, ik)
    for ar, ir in zip(a['graphs']['per_size'], ic['rows']):
        assert ar['m'] == ir['vertices']
        assert ar['graphs'] == ir['graphs']
        assert ar['partition_assignments'] == ir['partitions']
        for field in ('graph_partition_pairs', 'represented_typed_pairs'):
            assert ar[field] == ir[field]
    assert a['interfaces']['physically_executed_strings'] == ic['arrow_strings_physically_checked'] == 83
    ag, ig = a['six_vertex'], i['six_vertex_and_syntax']
    assert ag['family_members'] == ig['cross_family_graphs'] == 8192
    assert ag['cross_edge_bits'] == ig['cross_bits'] == 13
    assert ag['refined_blocks'] == ig['refined_blocks']
    assert ag['recursive_tree_evaluations'] == ig['recursive_family_tree_evaluations'] == 16384
    assert ag['full_encoding_roundtrips'] == ig['family_encoding_roundtrips'] == 16384
    ar, ir = a['relations'], i['relations']
    assert ar['relation_matrices'] == ir['matrices'] == 104
    assert ar['support_candidates'] == ir['support_candidates'] == 105
    assert ar['nonempty_support_fibres'] == ir['inhabited_support_fibres'] == 56
    for x, y in zip(ar['per_domain'], ir['rows']):
        assert (x['a'],x['b'],x['matrices'],x['nonempty_support_fibres']) == (y['a'],y['b'],y['relations'],y['support_fibres'])
    an, inn = a['relational_signature'], ir['primitive_certificate']
    assert an['carriers'] == inn['interfaces']
    assert an['R'] == matrix_edges(inn['R'])
    assert an['S'] == matrix_edges(inn['S'])
    assert an['composite'] == matrix_edges(inn['composite']) == [[0,0],[1,1]]
    assert an['whole'] == matrix_edges(inn['strict_whole'])
    assert a['mutations']['controls_executed'] == 8
    result = {'status':'PASS', 'author_source_sha256':a['source_sha256'],
              'independent_source_sha256':i['source_sha256'],
              'author_certificate_sha256':digest(ap), 'independent_certificate_sha256':digest(ip),
              'checked':'Exact domain counts, every size/domain row, inverse/fibre counts, named tree/occurrence/family counts, and the proof-aligned relation fixture.',
              'independence':'This comparator imports neither model; independent checker was implemented before author-source inspection.'}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
