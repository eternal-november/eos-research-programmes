#!/usr/bin/env python3
"""Create the text-first mathematical dossier from frozen proof/evidence inputs.
This is document assembly, not mathematical acceptance or proof verification.
"""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
ROOT=P.parents[1]
sections=[
 ('0. Confirmed parent disposition: technical verification and scientific shortfall',P/'ParentDisposition.md'),
 ('I. Independent local categorical completion, full arrow normal forms and necessity',P/'proof/Completion_Comparison.md'),
 ('II. Full semantic tuples, strongest product baseline, transport and factorization limits',P/'proof/Semantics_Transport_Factorization.md'),
 ('III. Exact standard operator-category comparison and significance finding',P/'proof/Operator_Baseline_Translation.md'),
 ('IV. Inherited complete mixed object-normalization proof (reused, not new credit)',ROOT/'research/workstream_A/rewrite/THEOREM.md'),
 ('V. Inherited exact A3 quotient linkage (reused; see explicit small-N clarification in I/II)',ROOT/'research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md'),
 ('V(b). Inherited decidability boundary and verified source attribution',ROOT/'research/workstream_A/rewrite/LIMITS_AND_SOURCES.md'),
 ('VI. Checked representative scope, exact P/L boundary and reproduction',P/'lean/README.md'),
 ('VII. Independent mathematical review',P/'review/MixedCompletion_IndependentPReview.md'),
 ('VIII. Independent operator-baseline review',P/'review/OperatorBaseline_IndependentPReview.md'),
 ('IX. Exact-hypothesis primary-source audit',P/'review/PriorTheory_ExactHypothesisAudit.md'),
 ('X. Primary-source precision addendum',P/'review/PriorTheory_ExactHypothesisAudit_Addendum.md'),
 ('XI. Independent Lean evidence and adversarial controls',P/'review/Lean_Independent_Review.md'),
 ('XI(b). Independently checked portable-harness addendum',P/'review/Lean_Portability_Addendum.md'),
 ('XI(c). Independently reviewed finite scope, actual execution and adversarial controls',P/'review/Finite_Independent_Review.md'),
 ('XI(d). Exact frozen finite domain',P/'finite/DOMAIN.md'),
 ('XI(e). Reproducibility, component receipts and limits',P/'REPRODUCTION.md'),
 ('XII. Scientific scope finding submitted for decision',P/'Gate2_ScopeFinding.md'),
 ('XIII. Failure and revision register',P/'FailureAndRevisionRegister.md'),
]
summary=(P/'ReportSummary.txt').read_text() if (P/'ReportSummary.txt').exists() else 'DRAFT: finite verification and parent disposition remain pending. Not a final acceptance report.\n'
parts=['WITNESSED DECOMPOSITIONS — INTEGRATED A4 / C5 / B3 TECHNICAL DOSSIER\n',summary,'\nCONTENTS\n'+'\n'.join(title for title,_ in sections),'\nEvidence conventions: P complete written proof; L named Lean-checked representative; C bounded executable check; X typed counterexample. Neither C nor L grants scientific acceptance.\n']
for title,path in sections:
 data=path.read_bytes();parts.extend(['\n'+'='*78+'\n'+title+'\n'+'='*78+'\n',f'Source: {path.relative_to(ROOT)}\nSHA256: {hashlib.sha256(data).hexdigest()}\n\n',data.decode()])
text='\n'.join(parts)
(ROOT/'Results_Integrated_A4_C5_B3.txt').write_text(text)
print(json.dumps({'path':str(ROOT/'Results_Integrated_A4_C5_B3.txt'),'bytes':len(text.encode()),'sha256':hashlib.sha256(text.encode()).hexdigest(),'status':'Assembly only; acceptance follows ReportSummary and parent decision'},indent=2))
