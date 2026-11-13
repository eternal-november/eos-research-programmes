#!/usr/bin/env python3
"""Source-only TeX checks. This is not compilation or visual validation."""
from pathlib import Path
import hashlib
import re


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    source = Path(__file__).resolve().parent.parent / 'report.tex'
    text = source.read_text(encoding='utf-8')
    no_comments = '\n'.join(re.split(r'(?<!\\)%', line)[0] for line in text.splitlines())
    stack = []
    for match in re.finditer(r'(?<!\\)[{}]|\\(?:begin|end)\{([^}]+)\}', no_comments):
        token = match.group()
        if token.startswith('\\begin'):
            stack.append(('environment', match.group(1)))
        elif token.startswith('\\end'):
            require(bool(stack), 'Unmatched environment end')
            require(stack.pop() == ('environment', match.group(1)), 'Mismatched environment')
        elif token == '{':
            stack.append(('brace', '{'))
        else:
            require(bool(stack), 'Unmatched closing brace')
            require(stack.pop() == ('brace', '{'), 'Mismatched closing brace')
    require(not stack, 'Unclosed groups or environments')
    labels = re.findall(r'\\label\{([^}]+)\}', text)
    refs = re.findall(r'\\(?:ref|eqref)\{([^}]+)\}', text)
    require(len(labels) == len(set(labels)), 'Duplicate labels')
    require(not (set(refs) - set(labels)), 'Unresolved references')
    bibliography = set(re.findall(r'\\bibitem\{([^}]+)\}', text))
    citations = set()
    for names in re.findall(r'\\cite(?:\[[^]]*\])*\{([^}]+)\}', text):
        citations.update(names.split(','))
    require(not (citations - bibliography), 'Unresolved citation keys')
    require('\\input{' not in text and '\\include{' not in text, 'External TeX dependency')
    print('PASS: balanced groups and environments; unique labels; resolved references and citations; self-contained source.')
    print(f'Labels: {len(labels)}; cited bibliography entries: {len(citations)}; lines: {len(text.splitlines())}')
    print('SHA256: ' + hashlib.sha256(text.encode()).hexdigest())
    print('These checks do not compile TeX or certify page layout.')


if __name__ == '__main__':
    main()
