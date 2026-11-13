# D2 source-to-obligation map

31 October 2026. Scope is exactly original D2, lines 382–396. This map
identifies proofs, reused results, and bounded evidence separately. It does
not mark the whole contract accepted or claim new L evidence for D2.

## 1. Authoritative contract and declared class

Authoritative source:
`/workspace/shared/contract_revision_20261028/final_artifacts/Original_Completion_Contract_v0.1_VERBATIM.md`

SHA-256:
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.

D2 class B starts at line 382. Line 384 asks for the extra hypotheses under
which noninvertible transport commutes with composition/decomposition. Line
386 requires starting from C2 and finite maps `f:A'→A`, `g:B'→B`, `h:C'→C`.
The declared class in `theorem.md` §1 is **all finite sets and all existing
total maps between them**, including empty carriers. Its all-path extension
uses arbitrary finite positive paths; its tree extension uses arbitrary
finite ordered incidence-compatible C2 diagrams with named intermediates.
The categorical extension is actual finite spans with actual apex/leg tables,
not an unspecified abstract equipment.

## 2. Contract discharge matrix

| Original requirement | Exact location in `theorem.md` | Proof level / limits |
|---|---|---|
| Composition of restrictions versus restriction of composite, line 388 | (2.1), with realization map `b'↦g(b')`; graph factorization (2.4) | P, all finite maps and all relations |
| Sharp equality criterion for meaningful map class, lines 388,396 | Theorem 2.1 fixed-relation image-hit criterion; Theorem 2.2 uniform iff `A'=∅ or C'=∅ or g surjective` | P; the criterion is evaluated from relation/map tables, not assumed comparison invertibility |
| Intermediate surjectivity and empty exceptions, line 388 | Theorem 2.2 proof and its following complete binary empty-case discussion | P; `B=∅` makes the existing `g` surjective, rather than adding a false exception |
| Arbitrary positive-path extension | Theorem 3.1: relation-specific tuple/image criterion and universal iff primed exterior empty, old internal empty, or every internal map onto | P, all finite lengths; separate unary case |
| Generalization or limitation theorem, line 388 | Theorem 5.1 complete-C2 global all-arity impossibility; §6 finite-span extension and Corollary 6.1 | P; includes all-primed-empty exception. Span fibre/all-tree theorem is imported, not rediscovered |
| Proved criterion and nontrivial positive family, line 390 | §5.1 internal-surjection family; image-supported subset inclusions with all permitted units; §7 controls 1,3,5 | P; actual noninvertible examples, not only bijections |
| Comparison map / inclusion / isomorphism / equality distinguished, line 390 | §1 four-level distinction; §2 inclusion/equality; §6 actual apex map and singleton-fibre isomorphism criterion | P; no inference from relation equality or apex equicardinality to comparison bijectivity |
| Non-surjective failure, positive surjective case, emptiness tests, line 392 | §7 controls 1–10, especially 1,2,6,7,8,10 | Explicit finite examples; independent C script checks them and exhaustive stated bounds |
| C2 dependency, line 394 | §§1,3–5 plus source ledger below | Reuses actual C2 components, all-arity calculus, substitution and incidence-chart definitions |
| D1 dependency, line 394 | End of §4.1 and §8; bijective specialization agrees with D1 §9 after reversing boundary-map directions | D1's equation/refinement checks are retained; arbitrary noninvertible primitive action is not assumed |
| Arbitrary-tree compatibility where claimed, line 396 | Theorem 4.1 and proof; §4.2 adjacent-pair failure; §6.1 retained-cut reuse | P, unbounded finite trees. Every named actual node/run/nullary is tested. Root-only and adjacent-primitive-only shortcuts excluded |
| Not merely elementary obstruction or assumed comparison invertibility, line 396 | Tables/realization sets (2.2), (3.1), image-hit test (3.3), fibre counts (6.2); exact global classification | Meets the requested mathematical form with explicit necessary-and-sufficient predicates |

## 3. Exact inherited source ledger

### C2 — the actual relation-interface model

Path:
`/workspace/shared/contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_C2/proof/C2_Model_Theorem.md`

SHA-256:
`15fcef7404272567dd957cb8f2b7a83ba40761034b589745a215adc233d315df`.

Reused locations:

* §§1–3: relation components retain their labels, full paths and whole;
  thin containment/exact operation fibres; R1–R3; full-arity substitution.
* §4: inverse-image restriction; R4 all-arity comparison; explicit tuple
  maps; separate nullary diagonal; R5 sufficient surjectivity/injectivity.
* §5.1: global base-changing containment map and occurrence-wise substitution.
* §5.2: local incidence-compatible charts, including nullary identifications;
  arbitrary finite-tree containment transport and coherence.
* §6: public A API bridge and precise difference between thin C2 semantic
  cells and primitive/free/presented witness labels.

The D2 additions relative to this source are the **sharp converses and empty
classification**, the fixed-relation versus uniform quantifiers, the complete
positive-path iff criterion, and the sharp complete-quiver all-arity
limitation. C2 itself explicitly declined to prove D2's sharp classification.
Its finite/sufficient facts are not renamed as a new theorem.

Inherited formal source, for context rather than a new D2 L claim:
`/workspace/shared/contract_revision_20261028/extracted/witnessed_decompositions/research/workstream_C2/lean/RelationInterface.lean`.
The companion refinement API is
`/workspace/shared/contract_revision_20261028/extracted/witnessed_decompositions/WitnessedDecompositions/RefinementFunctoriality.lean`.
This D2 work does not claim that these files contain the new iff statements
or that they were rebuilt as a fresh D2 formal certificate.

### D1 — specified bijective primitive/equation/refinement action

Path:
`/workspace/shared/d1_equivariant_transport_20261031/theorem.md`

SHA-256:
`1d814cb6c831b68c81ce38c20e72390a0194cc5f8ddd0d372b936d8f867ac165`.

Reused locations:

* §§2–5: supplied type/primitive maps, congruence invariance, strict action,
  and full occurrence-refinement comparison; none follows from bare names.
* §9.1: actual finite relation-interface bijective transport, its witness
  bijection, nullary equality, and recovery of C2.
* §9.2: the actual seven C5 equation families, not merely semantic equality.

D2 on bijections has exactly this relational behavior under the stated
variance conversion. D2 does not extend D1's arbitrary signature action
without separately supplying noninvertible primitive maps and equation checks.

### CUT — prior finite-span exactness and coherent cut transport

Path:
`/workspace/shared/contract_revision_20261028/structural_extracted/proof/Global_Cut_Repair.md`

SHA-256:
`2329adbd1844a9a62bfefe2094526d490c302acc639116a062590dd2d31ca449`.

Reused §10:

* (10.1) actual comparison from composite of endpoint restrictions to
  restriction of composite;
* (10.2) product of intermediate lift fibres, including empty feasibility;
* (10.3) separate diagonal unit comparison and injection criterion;
* actual composite child spans at every relevant run/node; adjacent-only
  vacuity control; all-tree certificate transport and successive-change
  coherence; distinction between root support and proper actual witness.

D2 §6 is explicitly an application of this prior theorem. It does not
present unique-lift/all-tree transport as a new discovery.

### I4 — retained-diagram and boundary-factorization precision

Path:
`/workspace/shared/i4_mixed_interchange_20261031/theorem.md`

SHA-256:
`cdcc40aeab3b0112737ae0c2765bf95821683e067bcad87adc722170b8ebd70d`.

Reused locations:

* §§1–2: actual retained records, actual maps versus support, B criterion,
  named run and nullary scope;
* §§3.2–3.3: endpoint-preserving coefficient comparisons and lift fibres;
* §3.3A: first restrict a map whose domain is an old composite, then use
  the separate comparison from individually restricted pieces;
* §3.4: all-depth tuple projection/grafting/contraction coherence;
* §3B: semantic occurrence tuples versus additionally retained primitive
  stages; D2 never silently replaces one with the other;
* §6: positive/negative controls, especially adjacent-pair vacuity and
  whole-support masking of an actual proper intermediate.

I4's full mixed grid/double-category/orbit theorem is not required for the
relational criterion. The original orbit branch does not authorize arbitrary
ambient-span quotient descent in D2.

## 4. Standard mathematical baseline and comparison note

The verified primary-source note is
`/workspace/shared/d2_d3_interface_descent_20261031/literature_comparison.md`.
Its §2.1 identifies Gambino–Kock, *Polynomial functors and polynomial monads*,
[arXiv:0906.4931v2](https://arxiv.org/pdf/0906.4931v2), §1.1–1.2, printed p.5,
for pullback/dependent-sum base change and Beck–Chevalley **under a cartesian
square hypothesis**. Its §3 directly compares existential support, actual
span fibres, and the separately changed provenance-groupoid doctrine.

The primary-source note is attribution and a bounded scientific-scope
comparison, not a substitute for the elementary proofs here. The ordinary
mechanisms are standard; the D2 deliverable is their precise parameterized
application/classification in the required C2/finite-Span setting. It is not
an originality claim and not an assertion that arbitrary interface squares
are cartesian.

## 5. Evidence boundary and independent review

* Mathematical proof source: `theorem.md`, no numerical/tree-depth bound.
* Independent finite check source: `../checks/d2_finite_checks.py`, with
  exact result/log artifacts recorded by the verifier in the shared checks
  directory. The tested domains are bounded and do not replace P.
* Independent mathematical/scope review: `../audit/acceptance.md`,
  with final-byte/hash disposition supplied by the auditor.
* Primary-source comparison: `../literature_comparison.md`.

The verifier reports exhaustive binary maps/relations at cardinalities ≤2,
ternary maps/relations at its explicitly stated endpoint/internal bounds,
empty/nullary/global-family controls, and all reduced ordered tree shapes
up to five leaves with actual nested witness and contraction comparisons.
The exact counts and final pass status belong to its machine-readable output
and report, not to an invented formal proof status. The author adds no
mandatory new Lean target: original D2 requires the proved criterion and
positive family/obstruction repair, while these finite C checks provide
additional independently replayable evidence.

Minimal inherited mathematical dependencies for a self-contained source
bundle are the five exact text sources hashed in §1/§3: original contract,
C2 model theorem, D1 theorem, CUT repair, and I4 theorem. Include their maps
or formal sources only if the report claims to reproduce those inherited
certificates; the D2 source itself does not rebuild them.
