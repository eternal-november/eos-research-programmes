#!/usr/bin/env python3
"""Structural checks only: not a TeX compiler or proof assistant."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parent
source=ROOT/'Applications_and_Boundaries_of_Result_Dependent_Interaction.tex'
s=source.read_text()
# Remove comments, respecting escaped percent signs.
s=re.sub(r'(?<!\\)%[^\n]*','',s)
errors=[]
stack=[]
for m in re.finditer(r'\\(begin|end)\{([^{}]+)\}',s):
    kind,name=m.groups()
    if kind=='begin': stack.append(name)
    elif not stack or stack.pop()!=name: errors.append('environment mismatch at '+str(m.start()))
if stack: errors.append('unclosed environments '+repr(stack))
depth=0
for m in re.finditer(r'(?<!\\)[{}]',s):
    depth+=1 if m.group()=='{' else -1
    if depth<0:errors.append('closing brace before opening');break
if depth:errors.append('unbalanced braces '+str(depth))
if len(re.findall(r'(?<!\\)\$',s))%2:errors.append('odd unescaped dollar delimiters')
for op,cl in [('\\[','\\]'),('\\(','\\)')]:
    if len(re.findall(r'(?<!\\)'+re.escape(op),s))!=len(re.findall(r'(?<!\\)'+re.escape(cl),s)):errors.append('unbalanced '+op)
labels=re.findall(r'\\label\{([^{}]+)\}',s)
if len(set(labels))!=len(labels):errors.append('duplicate labels')
refs=re.findall(r'\\(?:eqref|ref|pageref)\{([^{}]+)\}',s)
if set(refs)-set(labels):errors.append('undefined references '+repr(sorted(set(refs)-set(labels))))
bibs=re.findall(r'\\bibitem\{([^{}]+)\}',s)
cites=[k.strip() for group in re.findall(r'\\cite\{([^{}]+)\}',s) for k in group.split(',')]
if set(cites)-set(bibs):errors.append('undefined citations')
cases=re.findall(r'\\section\{Case ([A-I]) ',s)
if cases!=list('ABCDEFGHI'):errors.append('case roster/order '+repr(cases))
expected='19865f5dd71be317b36f77645c941026a55bde4a6cc94994d761badaffb290d3'
freeze_hash=hashlib.sha256((ROOT/'portfolio_selection.md').read_bytes()).hexdigest()
if freeze_hash!=expected: errors.append('authoritative freeze changed')
for needle in ['Sentinel\\_eac345cd1b8c8191b7dfc2cceb545b86','22:20:49','conditional','RejectInvariant','external linear','rig embedding','pointwise']:
    if needle not in s:errors.append('missing required textual boundary '+needle)
# Global terms whose accidental inclusion usually indicates an unedited draft.
for bad in ['TODO','FIXME','INSERT CASE','PLACEHOLDER']:
    if bad in s:errors.append('unfinished marker '+bad)
report={
 'status':'PASS' if not errors else 'FAIL',
 'scope':'Structural source validation only; not compilation, visual QA or proof-assistant verification',
 'source':source.name,'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'bytes':source.stat().st_size,'lines':source.read_text().count('\n'),
 'cases':cases,'full_cases':list('ABC'),'focused_cases':list('DEFGHI'),
 'labels':len(labels),'references':len(refs),'bibliography_entries':len(bibs),
 'environments_balanced':not stack,'brace_depth':depth,
 'frozen_roster_sha256':freeze_hash,
 'typesetting_status':{'compiled':False,'pdf_produced':False,'layout_reviewed':False,'scope':'Authorized uncompiled TeX source'},
 'independent_mathematical_review':{'status':'PASS' if hashlib.sha256(source.read_bytes()).hexdigest()=='bd01b4e25974a6822948c87f09813cd3b6bb327a59439bcd4cebade50f5b956d' else 'REVIEW_NEEDED','reviewed_source_sha256':'bd01b4e25974a6822948c87f09813cd3b6bb327a59439bcd4cebade50f5b956d','scope':'Human-readable mathematical and interpretation-scope review, not proof-assistant verification'},
 'errors':errors}
(ROOT/'O6_casebook_source_qa.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
if errors:sys.exit(1)
