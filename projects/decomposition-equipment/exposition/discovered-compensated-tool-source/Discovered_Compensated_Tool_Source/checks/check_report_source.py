#!/usr/bin/env python3
"""Static TeX and source-locator QA only; intentionally does not compile."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'writeup/Discovering_a_Compensated_Tool.tex'
raw = REPORT.read_text()
body = '\n'.join(re.split(r'(?<!\\)%', line, maxsplit=1)[0]
                 for line in raw.splitlines())

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

stack = []
for match in re.finditer(r'\\(begin|end)\{([^}]+)\}', body):
    kind, name = match.groups()
    if kind == 'begin':
        stack.append(name)
    else:
        require(bool(stack) and stack[-1] == name,
                f'Environment mismatch at {match.start()}: {name}')
        stack.pop()
require(not stack, f'Unclosed environments: {stack}')

depth = 0
for match in re.finditer(r'(?<!\\)[{}]', body):
    depth += 1 if match.group() == '{' else -1
    require(depth >= 0, f'Unmatched closing brace at {match.start()}')
require(depth == 0, 'Unclosed TeX groups')
require(len(re.findall(r'(?<!\\)\$', body)) % 2 == 0,
        'Odd number of inline math delimiters')
require(len(re.findall(r'(?<!\\)\\\[', body)) == len(re.findall(r'(?<!\\)\\\]', body)), 'Unbalanced display math')

labels = re.findall(r'\\label\{([^}]+)\}', body)
refs = re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', body)
require(len(labels) == len(set(labels)), 'Duplicate labels')
require(set(refs) <= set(labels), f'Missing labels: {set(refs)-set(labels)}')
bib = re.findall(r'\\bibitem\{([^}]+)\}', body)
cites = [key.strip() for group in re.findall(r'\\cite\{([^}]+)\}', body)
         for key in group.split(',')]
require(len(bib) == len(set(bib)), 'Duplicate bibliography keys')
require(set(cites) <= set(bib), f'Missing citations: {set(cites)-set(bib)}')
for marker in ('MODEL_AND_MAIN_THEOREM', 'MISSION_AND_FAILURES',
               'BRIDGE_INSTANCE', 'ASSURANCE_AND_BOUNDARIES', 'TODO', 'TBD'):
    require(marker not in raw, f'Unresolved marker: {marker}')

anchors = [
    ('reference_sources/relative/sources/stages/O4/'
     'Typed_Protocols_and_Bounded_Higher_Order_Interaction.tex',
     [r'\label{lem:execution}', r'\label{thm:substitution}']),
    ('reference_sources/relative/sources/stages/O5/'
     'Contextual_Refinement_and_Controlled_Recovery.tex',
     [r'\label{thm:replacement}', r'\label{lem:raw-lift}']),
    ('reference_sources/decomposition/formal_backbone/project/'
     'JointQuotientDecoder.lean',
     ['theorem quotient_exact_iff_stable',
      'theorem exact_iff_sound_and_sourceFixedLift',
      'theorem exact_compose_records', 'theorem generated_tests_preserved']),
    ('reference_sources/decomposition/stage_sources/'
     'return_cylinder_bridge_source/return_cylinder_bridge/theory/'
     'cylinder_priority_bridge_20261031/bridge_theorem.md', []),
]
sources = []
for relative, strings in anchors:
    path = ROOT / relative
    text = path.read_text()
    for string in strings:
        require(string in text, f'Missing source anchor: {relative}: {string}')
    sources.append({'path': relative,
                    'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                    'verified_anchors': strings})

receipt = {
    'status': 'PASS',
    'scope': 'Static source structure and exact local source anchors only',
    'compiled': False,
    'rendered': False,
    'report': str(REPORT.relative_to(ROOT)),
    'report_sha256': hashlib.sha256(REPORT.read_bytes()).hexdigest(),
    'labels': len(labels), 'bibliography_entries': len(bib),
    'whitespace_words_including_tex': len(raw.split()),
    'sources': sources,
}
output = ROOT / 'checks/report_source_qa.json'
output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps(receipt, indent=2, sort_keys=True))
