"""Deterministic source-only checks; does not invoke TeX or certify proofs/layout."""
from pathlib import Path
import re
import sys

path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name('Contextual_Refinement_and_Controlled_Recovery.tex')
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
for required in ('thm:main', 'sec:regime', 'sec:contexts', 'eq:obsorder',
                 'eq:local-matrix', 'thm:replacement', 'eq:bind-coupling',
                 'eq:native', 'eq:raw-lift', 'lem:raw-lift', 'eq:span',
                 'prop:vertical', 'prop:coverage', 'thm:representation',
                 'cor:persistent', 'eq:recovery-domain', 'thm:recovery',
                 'sec:acceptance'):
    assert required in labels, ('missing principal statement', required)
for required in ('CF-0.1', 'O4', 'O5', 'zero-weight', 'cost-exact',
                 'uncompiled', 'private store', 'joint', 'chronological',
                 'full abstraction', 'closing', 'Foxtrot', 'cartesian',
                 'reference cost'):
    assert required in s, ('missing scope safeguard', required)
print(f'PASS: {path.name}; {len(s.splitlines())} lines, {len(labels)} unique labels, '
      f'{len(refs)} resolved references, {len(bib)} bibliography entries; '
      'balanced groups/environments and math delimiter counts; no compilation.')
