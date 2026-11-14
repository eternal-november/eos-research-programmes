from pathlib import Path
import re,json
root=Path(__file__).resolve().parents[1]
issues=[]
for path in list((root/'notes').glob('*.tex'))+list((root/'sections').glob('*.tex'))+[root/'Native_Feedback_and_Shared_Content_First_Results.tex']:
    s=path.read_text();stack=[]
    for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',s):
        kind,name=m.groups()
        if kind=='begin':stack.append(name)
        elif not stack or stack.pop()!=name:issues.append(f'{path.name}: environment mismatch')
    if stack:issues.append(f'{path.name}: unclosed environments {stack}')
    # Standalone references checked per document, integrated section labels globally below.
    if path.parent.name=='notes' or path.name=='Native_Feedback_and_Shared_Content_First_Results.tex':
        labels=re.findall(r'\\label\{([^}]+)\}',s)
        refs=re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',s)
        if len(set(labels))!=len(labels):issues.append(f'{path.name}: duplicate labels')
        if set(refs)-set(labels):issues.append(f'{path.name}: missing labels {set(refs)-set(labels)}')
allsections=(root/'Native_Feedback_and_Shared_Content_First_Results.tex').read_text()
labels=re.findall(r'\\label\{([^}]+)\}',allsections)
refs=re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',allsections)
if len(labels)!=len(set(labels)):issues.append('Integrated duplicate labels')
if set(refs)-set(labels):issues.append('Integrated missing labels')
for path in root.glob('*.md'):
    for target in re.findall(r'\[[^]]*\]\(([^)]+)\)',path.read_text()):
        if '://' not in target and not (root/target.split('#')[0]).exists():issues.append('Missing local link '+target)
for path in root.rglob('*'):
    if path.is_file() and path.suffix in {'.tex','.md','.py','.json'}:
        # Never include private backup identifiers in tracked public-facing sources.
        if re.search(r'libfile_[A-Za-z0-9_-]+|file_[0-9a-f]{20,}',path.read_text()):issues.append('Private file identifier in '+str(path.relative_to(root)))
assert not issues,issues
out={'status':'passed','scope':'static source consistency, not TeX compilation or mathematical proof','standalone_sources':len(list((root/'notes').glob('*.tex'))),'integrated_unique_labels':len(labels)}
(root/'checks/source_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
