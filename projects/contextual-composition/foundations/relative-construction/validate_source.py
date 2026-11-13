#!/usr/bin/env python3
"""Static source checks only. This does not compile TeX or verify its layout."""
from pathlib import Path
import hashlib, json, re
root=Path(__file__).resolve().parent
paper=root/'delivery'/'One_relative_construction_for_context_content_and_effects.tex'
s=paper.read_text()
# Remove comments but retain escaped percent signs.
clean='\n'.join(re.split(r'(?<!\\)%',line)[0] for line in s.splitlines())
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^}]+)\}', clean):
    kind,name=m.groups()
    if kind=='begin': stack.append(name)
    else:
        assert stack and stack[-1]==name, ('environment mismatch',name,stack)
        stack.pop()
assert not stack, stack
level=0
for i,c in enumerate(clean):
    if c in '{}':
        n=0; j=i-1
        while j>=0 and clean[j]=='\\': n+=1; j-=1
        if n%2: continue
        level+=1 if c=='{' else -1
        assert level>=0, ('extra close brace',i)
assert level==0, ('brace imbalance',level)
labels=re.findall(r'\\label\{([^}]+)\}',clean)
refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',clean)
assert len(labels)==len(set(labels)), 'duplicate labels'
assert not set(refs)-set(labels), ('unresolved references',set(refs)-set(labels))
bibs=set(re.findall(r'\\bibitem\{([^}]+)\}',clean))
cites=[]
for m in re.finditer(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',clean): cites+=m.group(1).split(',')
assert not set(cites)-bibs, ('unresolved citations',set(cites)-bibs)
assert clean.count('\\begin{document}')==clean.count('\\end{document}')==1
assert not re.search(r'TODO|FIXME|PLACEHOLDER|turn\d+(?:search|view)',s)
assert s.count('$')%2==0, 'odd inline dollar count'
result={
 'status':'passed_static_checks', 'tex_compiled':False, 'layout_visually_verified':False,
 'scope':'Environment nesting, braces, labels/references, citation keys, document delimiters, placeholder scan and inline math parity. Not mathematical proof or TeX compilation.',
 'paper':paper.name, 'sha256':hashlib.sha256(paper.read_bytes()).hexdigest(),
 'bytes':paper.stat().st_size,'lines':len(s.splitlines()),'whitespace_delimited_words':len(s.split()),
 'labels':len(labels),'references':len(refs),'bibliography_entries':len(bibs),'citation_uses':len(cites)
}
(root/'static_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
