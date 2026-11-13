#!/usr/bin/env python3
"""Formula/source verification after a completed author run; not independent review."""
from pathlib import Path
from math import comb
import hashlib,json
p=Path(__file__).resolve().parent
r=json.loads((p/'AuthorCertificate.json').read_text());c=r['counts']
assert r['status']=='PASS'
assert r['domain_sha256']==hashlib.sha256((p/'DOMAIN.md').read_bytes()).hexdigest()
for n,h in r['source_sha256'].items():assert hashlib.sha256((p/n).read_bytes()).hexdigest()==h
sizes=(3,2,1)
T_expected=sum(14635+8112*m+1320*m*m+48*m*m*m for m in sizes)
assert sum(x['executed'] for x in r['T_rows'])==T_expected==112785
H_expected=sum(sizes)*sum((sum(2**(n*(n-1)//2)*k**n for n in range(3)))*comb(k+3,2) for k in range(4))
assert c['H_sources']==H_expected==2802
F_expected=sum(sizes)*sum((sum(2**(n*(n-1)//2)*k**n for n in range(3)))*comb(k+3,2)*sum(k-q+1 for q in range(2,k)) for k in (3,4))
assert r['F_exhaustive_cases']==F_expected==27270
assert c['factorization_cases']==F_expected+5*sum(sizes)==27300
assert c['category_associativity']==comb(6,2)*8==120
assert c['literal_bound_inclusions']==4
assert c['tower_heights']==135
assert c['Hcomp_raw_pairs']==c['Hcomp_pairs']
assert c['six_label_tuples']==sum(m**5 for m in sizes)==276
assert c['six_positional_split_value_assignments']==276
assert c['MIn_union_unique']==147+102+67==316
assert c['MIn_union_unique']==c['MIn_base_unique']+c['MIn_expanded_unique']
assert c['factor_full_unary_probes']==c['factor_empty_interval_probes']==5*sum(m**3 for m in sizes)==180
assert c['unary_to_nullary_value_pairs']==3*sum(m*m for m in sizes)==42
v={'status':'PASS','author_certificate_sha256':hashlib.sha256((p/'AuthorCertificate.json').read_bytes()).hexdigest(),'domain_sha256':r['domain_sha256'],'independent_formula_counts':{'T':T_expected,'H_sources':H_expected,'F_exhaustive':F_expected,'F_with_named_six':27300,'six_label_tuples':276},'evidence':'same-author independent formulas/source binding, not non-author review'}
(p/'AuthorVerification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
