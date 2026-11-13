"""Deterministic source-only checks; does not invoke TeX or certify proofs/layout."""
from pathlib import Path
import re
import sys

path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('Law_and_Possibility_Repair_for_Dependent_Protocols.tex')
s = path.read_text(encoding='utf-8')
lines = []
for line in s.splitlines():
    m = re.search(r'(?<!\\)%', line)
    lines.append(line[:m.start()] if m else line)
t = '\n'.join(lines)
assert not any(ord(c)<32 and c!='\n' for c in t), 'unexpected control character'
assert ',,T' not in t, 'duplicated punctuation'
assert t.count(r'\documentclass') == 1
assert t.count(r'\begin{document}') == t.count(r'\end{document}') == 1
assert t.rstrip().endswith(r'\end{document}')
stack = []
for m in re.finditer(r'\\(begin|end)\{([^{}]+)\}', t):
    kind, name = m.groups()
    if kind == 'begin':
        stack.append((name, t.count('\n', 0, m.start())+1))
    else:
        assert stack and stack[-1][0] == name, (kind, name, stack[-1:])
        stack.pop()
assert not stack, stack
braces = []
for i, c in enumerate(t):
    # Escaped iff preceded by an odd run of backslashes.
    j = i - 1
    while j >= 0 and t[j] == '\\':
        j -= 1
    escaped = (i-j-1) % 2
    if c == '{' and not escaped:
        braces.append(i)
    elif c == '}' and not escaped:
        assert braces, ('extra closing brace', t.count('\n',0,i)+1)
        braces.pop()
assert not braces, [('unclosed brace',t.count('\n',0,i)+1) for i in braces]
labels = re.findall(r'\\label\{([^{}]+)\}', t)
assert len(labels) == len(set(labels)), 'duplicate labels'
refs = re.findall(r'\\(?:ref|eqref)\{([^{}]+)\}', t)
assert set(refs) <= set(labels), ('unresolved references', set(refs)-set(labels))
bib = re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}', t)
assert len(bib) == len(set(bib)), 'duplicate bibliography keys'
cites = [x.strip() for z in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^{}]+)\}', t) for x in z.split(',')]
assert set(cites) <= set(bib), ('unresolved citations',set(cites)-set(bib))
assert len(re.findall(r'(?<!\\)\\\[',t)) == len(re.findall(r'(?<!\\)\\\]',t)), 'display delimiters'
assert len(re.findall(r'(?<!\\)\$',t)) % 2 == 0, 'inline math delimiter parity'
for token in ('TODO', 'TBD', 'FIXME', 'INSERT PROOF', 'PLACEHOLDER'):
    assert token not in t, ('unresolved placeholder', token)
for required in ('thm:main', 'thm:obstruction', 'prop:M', 'thm:K',
                 'cor:forget', 'thm:interpretation', 'prop:predicates',
                 'prop:exact-span', 'prop:direct-boundary', 'thm:span',
                 'thm:contextual', 'prop:vertical', 'prop:E',
                 'thm:O1-input', 'prop:E-native', 'thm:reflection',
                 'thm:application', 'sec:ledger', 'sec:sources', 'sec:acceptance'):
    assert required in labels, ('missing principal statement', required)
for required in ('zero-weight', 'cost-exact', 'candidate possibility coverage',
                 'all-present', 'not a semiring section', 'not faithful',
                 'not a global equivalence', 'finite related-input carrier',
                 'need not be generated', 'private state', 'joint', 'fibrewise',
                 'raw multiplicity', 'strict positivity', 'not a general',
                 'Varacca', 'Goy', 'Fritz'):
    assert required in re.sub(r'\s+', ' ', s), ('missing scope safeguard', required)
import hashlib
import json
report = {
    'status': 'passed', 'file': path.name,
    'sha256': hashlib.sha256(s.encode('utf-8')).hexdigest(),
    'lines': len(s.splitlines()), 'words': len(s.split()),
    'labels': len(labels), 'references': len(refs),
    'bibliography_entries': len(bib),
    'checks': ['balanced braces', 'nested environments', 'resolved references',
               'resolved citations', 'math delimiter parity',
               'principal statements present', 'scope safeguards present'],
    'scope': 'Source-only validation, not compilation, visual QA, or proof certification.'
}
path.with_name('source_integrity_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
