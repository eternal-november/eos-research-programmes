from pathlib import Path
from datetime import datetime,timezone
import shutil,hashlib,json
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
parts=ROOT/'parts'
def segment(t,start,end):
 return t[t.index(start):t.index(end)]
gen=(BASE/'evolving_bridge_research_20261105/evolving_incidence_source_ready.tex').read_text()
p1=segment(gen,r'\section{Scope and independent source data}',r'\section{Supported topology and the actual partial-action domains}')
p1=p1.replace(r'\section{Scope and independent source data}',r'\section{Native programs generate the experimental doctrine}\label{sec:source}')
p1=p1.replace(r'\section{Growth forces a mixed-variance comparison}',r'\section{Growth forces a mixed variance comparison}\label{sec:growth}')
p1=p1.replace(r'\section{Three independent exactness conditions}',r'\section{Three distinct tests for an unchanged characterization}\label{sec:repair}')
assert r'\emph{entire resulting}' in p1 and 'including old operations acting on newly introduced tests' in p1
(parts/'01_generated_doctrine.tex').write_text(p1)
p3=segment(gen,r'\section{Deriving when wiring and completion commute}',r'\section{An automata change and noncommuting repairs}')
p3=p3.replace(r'\section{Deriving when wiring and completion commute}',r'\section{When generated completion commutes with actual wiring}\label{sec:wiring}')
p3=p3.replace(r'\section{A native interaction that repairs FCA without refining states}',r'\section{A two bit interaction separates the three changes}\label{sec:cnot}')
(parts/'03_wiring_cnot.tex').write_text(p3)
comp=(BASE/'interface_composition_theorem_20261105_1420/source_ready_section.tex').read_text()
p4=segment(comp,r'\section{What is supplied, and what changes}',r'\section{Verification scope}')
p4=p4.replace(r'\section{What is supplied, and what changes}',r'\section{Changing the formation of composite experiments}\label{sec:decomposition}')
p4=p4.replace(r'\section{The actual directed comparison}',r'\section{The directed comparison and its exact factorization criterion}')
p4=p4.replace(r'\section{A complete resource-matrix specialization}',r'\section{A complete classification for integer resource changes}\label{sec:resources}')
p4=p4.replace(r'\section{The exact connection to state, concept, and topology semantics}',r'\section{The exact response bridge to heterogeneous characterizations}\label{sec:slice}')
p4=p4.replace('a natural cone','a natural cocone').replace('pulled-back cone','pulled-back cocone').replace('pulled-back-cone','pulled-back-cocone')
p4=p4.replace('If the labelled tests carry\nspecified program-precomposition actions and the comparison is equivariant,\nthe corresponding actions and their stated domains transport as well.', 'For the same supplied deterministic state and program interpretation, if the\nlabelled tests carry specified program-precomposition actions and the\ncomparison is equivariant, the corresponding quotient and concept actions,\nand the object-nerve action spans with their stated domains, transport as well.')
p4=p4.replace('Equivariance gives the action assertion\nby the defined action formulas, without adding a lifting theorem.', 'Equivariance identifies the induced quotient and concept actions by their\ndefined formulas. The common supplied state maps give the same vertex maps\non the object nerves, and the common response columns give their domains.\nThis does not infer equality of raw state maps from nonseparating tests.')
insert=r'''
\paragraph{A response-level realization of the batch obstruction.}
In the batch example $C=(2)$ and source budget $1$, let each component
have a single experiment $e_i$, available at physical budget at least $1$.
Let the actual joint state set be $S=\{0,1\}^2$, and let $e_i$ ask
whether its component bit is $1$. At physical budget $2$ the joint
experiment has response column $\{(1,1)\}$, given by the intersection
of the two cylinders. After local interface change, each experiment needs
one whole source packet, so no joint label exists at source budget $1$.
Restrict attention to this prescribed paired-test family: no zero-budget
no-op test was supplied to either input diagram. Individually executable
probes on the joint carrier are not being counted. The source paired-test
family is empty; the target has one response column. Their row quotients have respectively one and two classes, their
extent families one and two elements, and their object nerves respectively
no vertices and one vertex. This is an actual incidence consequence of
an absent decomposition, under the stated independent-test interpretation.
By contrast, the two disconnected provenance allocations for $C=(1\ \ 1)$
can evaluate to the same response column. They then obstruct label-level
Set exactness without changing any of these extensional invariants.
'''
p4=p4.replace(r'\section{Coherence and the limits of the claim}',insert+'\n'+r'\section{Coherence of successive interface changes}')
(parts/'04_composition_resources.tex').write_text(p4)
files=['00_opening.tex','01_generated_doctrine.tex','02_supported.tex','03_wiring_cnot.tex','04_composition_resources.tex','07_native.tex','08_contextads.tex','09_prior_limits.tex','10_bibliography.tex']
text='\n\n'.join((parts/x).read_text() for x in files)
out=ROOT/'Changing_experiments_and_composing_characterizations.tex'
out.write_text(text)
stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
cp=ROOT/'checkpoints'/f'{stamp}_manuscript.tex'; cp.parent.mkdir(exist_ok=True); shutil.copy2(out,cp)
(ROOT/'assembly_manifest.json').write_text(json.dumps({'assembled_utc':stamp,'parts':files,'output':out.name,'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'checkpoint':str(cp.relative_to(ROOT))},indent=2))
print(json.dumps({'output':str(out),'bytes':out.stat().st_size,'lines':len(text.splitlines()),'checkpoint':str(cp)},indent=2))
