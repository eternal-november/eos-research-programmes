#!/usr/bin/env python3
"""Deterministic TeX/source-address checks of repository sources; not proof checking."""
from pathlib import Path
import argparse, hashlib, json, re, sys
parser=argparse.ArgumentParser()
parser.add_argument('--source',type=Path,default=Path(__file__).resolve().parent/'Integrated_Relative_Computation_Acceptance_Dossier.tex')
parser.add_argument('--sources-root',type=Path,default=Path(__file__).resolve().parent.parent)
parser.add_argument('--foundation',type=Path,default=None)
args=parser.parse_args()
raw=args.source.read_text(); s=re.sub(r'(?<!\\)%[^\n]*','',raw)
errors=[]; stack=[]
for m in re.finditer(r'\\(begin|end)\{([^{}]+)\}',s):
 kind,name=m.groups()
 if kind=='begin':stack.append(name)
 elif not stack or stack.pop()!=name:errors.append(f'environment mismatch {name} at {m.start()}')
if stack:errors.append('unclosed environments: '+str(stack))
depth=0
for m in re.finditer(r'(?<!\\)[{}]',s):
 depth+=1 if m.group()=='{' else -1
 if depth<0:errors.append('early closing brace');break
if depth:errors.append('brace depth '+str(depth))
for op,cl in [('\\[','\\]'),('\\(','\\)')]:
 if len(re.findall(r'(?<!\\)'+re.escape(op),s))!=len(re.findall(r'(?<!\\)'+re.escape(cl),s)):errors.append('unbalanced '+op)
if len(re.findall(r'(?<!\\)\$',s))%2:errors.append('odd dollars')
labels=re.findall(r'\\label\{([^{}]+)\}',s)
refs=re.findall(r'\\(?:eqref|ref|pageref)\{([^{}]+)\}',s)
if len(set(labels))!=len(labels):errors.append('duplicate internal labels')
if set(refs)-set(labels):errors.append('undefined refs '+str(sorted(set(refs)-set(labels))))
bibs=re.findall(r'\\bibitem\{([^{}]+)\}',s)
cites=[k.strip() for g in re.findall(r'\\cite\{([^{}]+)\}',s) for k in g.split(',')]
if set(cites)-set(bibs):errors.append('undefined cites '+str(sorted(set(cites)-set(bibs))))
resolved={};source_text={}
paths={
 'CT':'contracts/Expanded_Research_Contract_v0_1.tex',
 'O1':'interaction/independent-criterion/General_Independent_Interaction_Criterion.tex',
 'O2':'framing/External_Framing_and_Representation_Comparison.tex',
 'O3':'protocols/plural-semantics/Plural_Semantics_for_Result_Dependent_Protocols.tex',
 'O4':'protocols/higher-order/Typed_Protocols_and_Bounded_Higher_Order_Interaction.tex',
 'O5':'protocols/refinement-recovery/Contextual_Refinement_and_Controlled_Recovery.tex',
 'O6':'applications/Applications_and_Boundaries_of_Result_Dependent_Interaction.tex',
 'O7':'protocols/law-and-possibility/Law_and_Possibility_Repair_for_Dependent_Protocols.tex',
 'U':'foundations/relative-construction/delivery/One_relative_construction_for_context_content_and_effects.tex',
}
for sid,relative in paths.items():
 p=args.foundation if sid=='U' and args.foundation else args.sources_root/relative
 if not p.is_file():
  errors.append(f'missing source for {sid}: {relative}')
  continue
 resolved[sid]={'source':relative,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
 source_text[sid]=p.read_text()
addresses=re.findall(r'\\Addr\{([^{}]+)\}\{([^{}]+)\}',s)
for sid,label in addresses:
 if sid.startswith('#'):continue
 if sid not in source_text:errors.append('unresolved source '+sid)
 elif '\\label{'+label+'}' not in source_text[sid]:errors.append('unresolved external address '+sid+':'+label)
required=['A01','A32','S01','S07','sec:C-posterior','sec:C-span','thm:reflection','candidate possibility coverage','surjective','three full','six focused']
for phrase in required:
 if phrase not in s:errors.append('missing boundary '+phrase)
for phrase in ['TODO','FIXME','PLACEHOLDER','pending the acceptance review','Disposition remains explicit']:
 if phrase in s:errors.append('unfinished/stale marker '+phrase)
report={'status':'PASS' if not errors else 'FAIL','source':args.source.name,'sha256':hashlib.sha256(args.source.read_bytes()).hexdigest(),'bytes':args.source.stat().st_size,'lines':raw.count('\n'),'internal_labels':len(labels),'internal_references':len(refs),'external_source_addresses':len(addresses),'bibliography_entries':len(bibs),'citations':len(cites),'source_identities':resolved,'compiled':False,'rendered':False,'proof_assistant_verified':False,'scope':'Structural TeX source and external-address checks against current repository sources only; not proof checking or original-archive identity verification','errors':errors}
output=args.source.parent/'integrated_source_qa.json';output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2));sys.exit(bool(errors))
