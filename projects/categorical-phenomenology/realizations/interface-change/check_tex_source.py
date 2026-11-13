#!/usr/bin/env python3
"""Limited static checks only. This is not TeX compilation or rendered QA."""
from pathlib import Path
import re
import json

source = Path(__file__).with_name('report.tex').read_text()
labels = re.findall(r'\\label\{([^}]+)\}', source)
refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', source)
bibs = re.findall(r'\\bibitem\{([^}]+)\}', source)
cites = [key for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', source) for key in group.split(',')]
def require(condition, message):
    if not condition:
        raise RuntimeError(message)
require(len(labels) == len(set(labels)), 'Duplicate TeX labels')
require(not set(refs) - set(labels), f'Unresolved references: {set(refs) - set(labels)}')
require(not set(cites) - set(bibs), f'Missing bibliography keys: {set(cites) - set(bibs)}')
stack = []
for match in re.finditer(r'\\(begin|end)\{([^}]+)\}', source):
    operation, env = match.groups()
    if operation == 'begin':
        stack.append(env)
    else:
        require(bool(stack) and stack[-1] == env, f'Mismatched environment {env}')
        stack.pop()
require(not stack, 'Unclosed TeX environments')
text = re.sub(r'(?<!\\)%[^\n]*', '', source)
text = re.sub(r'\\[{}]', '', text)
depth = 0
for char in text:
    if char == '{': depth += 1
    if char == '}': depth -= 1
    require(depth >= 0, 'Unbalanced closing brace')
require(depth == 0, 'Unbalanced braces')
print(json.dumps(dict(file='report.tex', labels=len(labels), references=len(refs), bibliography_entries=len(bibs), cited_keys=len(set(cites)), environments_balanced=True, braces_balanced=True, duplicate_labels=False, unresolved_references=[], missing_bibliography_keys=[]), indent=2))
