# D1 — source reuse and obligation map

## Finding

The located sources already contain the free/presented calculus and full
occurrence-refinement infrastructure, plus concrete parameter transport and
coherent normal sections. The new `theorem.md` supplies the arbitrary strict
groupoid-action integration: primitive-data construction, exact descent
criterion, equivariant universal properties, full global refinement actions,
and local incidence-chart comparisons. The finite L action is separately
identified rather than misrepresented as a formalization of the entire proof.

Original target: `Original_Completion_Contract_v0.1_VERBATIM.md`, lines 366–380,
D1, not D2 and not a replacement completion contract. The review's statement
that full arbitrary-action coverage was not located is an evidence gap,
not proof that none existed elsewhere. No original ledger or source was edited.

## Exact obligation-to-result table

| Original D1 item | Result in `theorem.md` | Evidence and qualification |
|---|---|---|
| Specified allowed groupoid of interface changes | §§2.1,3.1 | Arbitrary small strict groupoid diagram of typed signatures; additionally arbitrary interface groupoid, component bifunctor and full-profile primitive action. Not restricted to endpoint names or one example. |
| Actions on component types and primitive witnesses | §§2.1–2.2,3.1–3.2 | Supplied at primitive/type level and extended by tree induction. No completed action assumed. Arbitrary parallel primitive permutations permitted. |
| Witness/substitution compatibility | (2.2), (3.1) | All independently prescribed child profiles, original occurrences, zero-length blocks and arbitrary tree depths. Local boundary maps pulled back through cumulative leaf offsets. |
| Identity and composition laws | (2.3)–(2.4), §§3.2–3.3 | Strict equalities of actual maps. Mathematical equality, not undocumented Lean definitional equality. |
| Descend through invariant equations | Theorem 2.1, §3.3 | Exact iff criterion is preservation of the generated congruence on declared pairs; literal declaration stability is stronger, not necessary. Proved using A3 derivation induction. |
| Check relation invariance, not assume it from names | §9.2 | All seven C5 families R/UL/UR/D0/DA/DL/DR checked at actual image grade, graph and monoid labels. Separate path-basis check for the stronger completion comparison. |
| Equivariant free universal property | (2.7), §3.2 | Construct extension by existing A2; derive its equivariance, inverse restriction/extension laws and naturality. |
| Equivariant presented universal property | (2.8), §3.3 | Existing A3 quotient factor; equivariance by precomposition with surjective projection. Not a biuniversal/2-categorical claim. |
| Coherent refinement comparison functors | §§4–5 | Actual original-slot tuple functors; global strict actions; strict inverse local charted-category functors; equality on successive local transports and explicit source/target projections. |
| Interface changes at individual positions | §§3,5.4,9.3 | Independent arrows at repeated boundary occurrences; incidence identifications and nullary shared boundary enforced. Uncharted global action is a specialization, not the only case. |
| Strict or coherent convention | §1, (4.3), (5.5), §8 | Strict supplied action and strict induced action; noncanonical normal sections use explicit natural isomorphisms with identity/cocycle laws where the independent completion theorem applies. No unproved weak-action strictification. |
| Nontrivial permutations of finite interface sets | §§9.1,9.3 | Three labelled Fin-3 carriers, action (S3)^3 on actual relation entries, including (9.4). Formal certificate has its own exact scope. |
| Composite relabelings | (9.1)–(9.3), §9.3 | Image relations compose by actual composite carrier permutations; internal tuple coordinates biject via shared middle map. |
| Repeated occurrences | §§4–5, (9.5) | Equal repeated component types remain distinct slots. Decoration vectors (0,0)/(1,1) yield unequal parallel endomorphisms with the same total. |
| Non-invariant relation that does not descend | §6 | Swap primitive a,b, fix z, equation a=z. Image b=z not derivable by independent b-count model; not merely absent from declaration list. |
| Isoclasses versus retained witnesses | §7 | Actual Grothendieck transport/refinement arrows retain groupoid arrow and refinement tuple; stabilizers lost by object isoclasses. Finite Z/3 orbit substitution is not well defined. |
| Arbitrary allowed actions in declared class | §§2–5 | Uniform theorem, no finiteness bound and no special normalizer assumed. Local compatibility is necessary typing data, not a postulated action on a quotient. |
| L for finite typed action example | Separate `formal/` source and verification report | Exact accepted declaration list, compiler/version, logs and limits must be read from formal verification output; P theorem does not itself claim these build results. |

## Source-first reuse table

Paths below are relative to the inherited source root
`/workspace/shared/contract_revision_20261028/extracted/witnessed_decompositions`.
Exact SHA-256 values and byte lengths are in `source_hashes.json`.

| Inherited source | Precisely reused | New work here / limitation |
|---|---|---|
| `research/workstream_A/A2_AdjunctionProof.md`, §§1–6 | Actual free extension, uniqueness among all strict maps, source/target naturality, primitive convention and universe scope. | Base-changing and locally transported actions constructed explicitly from primitive data. Source theorem is fixed-base; no bare invocation silently changes its base. |
| `research/workstream_A/A3_PresentedUniversalProof.md`, §§1–4; `A3_QuotientConstruction.md` | Least parallel substitution congruence, actual quotient, proof of substitution descent, exactness, hom bijection and uniqueness through surjective projection. | General and local equation-action descent criterion; equivariant factorization and universal property. |
| `WitnessedDecompositions/FreeExtension.lean` | Implemented free extension and strict uniqueness underlying the A2 source. | No modification or claim that full D1 is already in this module. |
| `WitnessedDecompositions/SemanticRefinement.lean` | Full occurrence tuples; category laws; whole profiles retained; morphism functor construction. | Base-changing action formulas and charted local refinement categories are supplied in P. |
| `WitnessedDecompositions/RefinementFunctoriality.lean` | Strict identity/composite/inverse refinement functor laws for same-base maps. | All-base extension proved entrywise, with actual source/target profiles specified. |
| `research/workstream_integration/proof/Semantics_Transport_Factorization.md`, §§2,4–5 | Full semantic arrow coordinates; parameter transport and strict squares; normal-section cocycle; seven equation and path-basis transport check. | Arbitrary signature/local-interface action theorem and finite relation specialization. Existing scoped parameter theorem is credited, not recreated as novelty. |
| `research/workstream_integration/proof/Completion_Comparison.md`, §§1–5 | Independent Comp category with raw/equation generators, O/MOut/MIn relations, coherent normalization and full-tuple comparison. | §8 extends comparison only for basis-preserving actions; operation-equation invariance alone is not claimed to act on an arbitrary chosen path presentation. |
| `research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md`, §§1–7 | Actual finite C5 signature and seven typed equations; identification with the actual A3 quotient; independent FlatCut and proved strict isomorphism. | Local carrier permutations and image-label invariance; equivariance of the existing semantic comparison. |
| `research/workstream_C2/proof/C2_Model_Theorem.md`, §§1–6 | Relation components, exact/containment calculus, tuple maps for bijections, incidence compatibility and all-arity/nullary distinctions. | Finite group action and presentation/refinement integration; no noninvertible D2 sharp criterion claimed. |
| `contract_review_20261031/structural_coverage.md`, D1; `current_coverage_insert.md`, D1 | Requested coverage gap and warning against restarting existing parameter transport. | Exact D1 conjunction now mapped to theorem/certificate; governance acceptance remains distinct. |

## Matching the finite formal action to the P example

The formal action uses three distinct labelled interfaces and an explicit
three-point carrier equivalent to `Fin 3`, with independent permutations at
each interface. Relation transport is (9.1), typed exact binary primitives
retain a Boolean decoration, and expression/forest transport preserves the
original leaf positions. Its checked binary decorated rotation is a
**derived** instance of the C5 seven-equation presentation, not the assertion
that its formal relation is definitionally the whole C5 congruence:

    k(l(u,v),w)  ~  l(u,k(v,w)).

Here a binary vertex carrying decoration `k` is translated as `d_k(c(-,-))`.
Both sides derive, by DL/DR and DA followed by R, to the same right comb with
root decoration `k+l` in `Z/2`. More explicitly, the left moves the inner
`l` through the left input by DL and combines decorations by DA, then R;
the right moves the inner `k` through the right input by DR and combines
by DA. Commutativity `k+l=l+k` identifies the totals. Interface composition
and graph-cut labels are the very typed labels verified in §9.2.

The formal `Expr.Derives` is a contextual rotation closure; it is not
advertised as the actual public A3 substitution-stable congruence, and its
full-profile parallelism is not a separately checked declaration. The P
translation maps every formal rotation/context step to a genuine C5
derivation; no converse completeness is needed or claimed.

The formal expressions therefore embed in the N=0 C5 family over the finite
relation category, with all graph partitions empty but all actual relation
grades and primitive decorations retained. A relation leaf translates to the
identity leaf of the corresponding component, a unit to the designated
nullary, and binary nodes as above. Typed leaf replacement translates to
occurrence-wise grafting because the replacement has exactly the leaf's
output relation. No interpretation of intermediate existential tuples as
extra C2 thin-cell proofs is made. Full decorated-operation presentation and
normalization are inherited P results; this finite formal fragment is a
representative D1 action/transport certificate, not a new complete C5 Lean
adapter. The additional checked `D1OriginalAPIBridge.lean` does construct a
genuine original `Signature`, `exactAssignment` into C2 `exactCalc`, and the
actual A2 `Tree.extend` map, with primitive output/profile and full typed
path transport/evaluation laws. It does not supply a generic changed-quiver
`Calc.Hom` or formalize all refinement-category laws. The executable finite
tests cover additional seven-template checks
only at their reported finite domain.

## Controls and nonclaims

1. A source quotient does not acquire transport by silently adding an orbit of
   missing equations. §6 supplies an actual separator for failure to descend.
2. Arbitrary weak actions have not been strictified. The class chosen is strict,
   and every comparison's equality/isomorphism level is stated.
3. Arbitrary operation-equation invariance does not imply preservation of a
   chosen higher/path-relation basis. General D1 refinement uses Ref(P), while
   §8 imports Comp only with its extra verified basis preservation.
4. Arbitrary endpoint pairs do not supply uncharted internal-interface changes.
   The exact local replacement is an explicitly defined charted functor span
   and strict inverse equivalence. Unequal maps at a nullary identified boundary
   are ill typed; the diagonal/antidiagonal control proves why this matters.
5. The transported calculus retains full whole components, paths, primitive
   multiplicities and independent tuple entries. It does not quotient by
   isomorphism class, orbit, equal total decoration, or equal final composite.
6. Full D2, D3, other original obligations and whole-program closure remain
   outside this D1 submission. Nothing edits historical acceptance records.
