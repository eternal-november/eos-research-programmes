# Original F4 obligation and evidence map

31 October 2026. This map does not amend the original contract. It separates
this F4 submission from historical source status and broader acceptance.

## Designated map

The primary source is the original **discrete M=1 typed ordered graph-cut
simplicial set**, not the ordinary refinement nerve. A degree-n record retains
one simple ordered graph, an arbitrary ordered n-partition of its vertices
(empty and noncontiguous blocks allowed), and the full actual composable
K-arrow path. The target retains the same ordered vertices, partition, and
actual arrow path; it omits only the adjacency relation. The whole map in
degree one is `(G,h) -> ([v],h)`.

C1 sections 1 to 3 provide the literal carriers, induced restriction identities,
and path-composition laws. CUT sections 1 to 4 provide the all-degree exact cut
construction and original discrete slice. The optional span-groupoid extension
retains its span and comparison-bijection data; forgetting additional fields
would be a different map, not the designated theorem.

## Clause to evidence

- **All-degree positive theorem, map directions, cartesian squares:**
  proof/F4_Edge_Forgetting_Theorem.md sections 1 to 3. For every active
  alpha:[m]->[n], the comparison is X_n -> X_m x_(Y_m) Y_n. Its inverse uses
  the coarse source whole graph and the fine target partition and arrow path.
  Activity keeps all vertices, so no omitted edges are guessed.
- **Conservativity, units, and all degrees:** the same proof includes all
  codegeneracies, endpoint insertions, zero degrees, and constant active maps
  into [0]. Empty graph components with nonidentity arrows are not units.
- **Noninjectivity and nonidentifiability:** section 4 supplies different
  graphs on the same two ordered vertices, with the same actual arrow. The
  whole fibre over ([v],h) has exactly 2^(v(v-1)/2) elements. Noninjectivity
  requires a nonempty K and an allowed graph size at least two; the original
  three-object, N>=6 family meets both conditions.
- **Genuine duplicated-witness failure:** section 6 defines a normalized
  C2 triangle-cocycle simplicial extension in every degree. Its two binary
  witnesses have identical whole, inputs, partition, and arrow path. The
  long-edge lifting comparison has two lifts. This extension is not 2-Segal;
  its higher coherence is proved, not assumed from degree-two duplication.
- **Separate supplementary control:** section 6.1 uses X x N(C2), which is
  unital 2-Segal but also fails fixed-whole lifting. Its two factor decorations
  differ, so it does not replace the identical-input witness control.
- **Finite computation:** evidence/verify_f4.py, verification_readme.md,
  results.json, and run.log give the exact bounded checks and replayable
  results. The graph and arrow-path coordinates are factorized; the full
  graph-times-path product is not claimed to have been physically enumerated.
- **Non-author correctness and scope assessment:** review/F4_Scoped_Review.md
  states the separate verdicts, replay provenance, and assurance limitations.

## Numerical bounds and acceptance boundary

The original F4 clause requires P and C, plus X for nonidentifiability, but
specifies no numerical enumeration bound. Its prescribed tests are different
edges on the same ordered vertices, unique lifting with the graph fixed, and
a deliberately duplicated cut-witness failure. A two-point-to-point discrete
example alone cannot replace its all-degree lifting argument.

F2 separately specifies all ordered graphs through four vertices and
simplicial degree four, plus mandatory six-vertex mixed-interface witnesses.
It permits documented equivalent factorized checking with an all-parameter
justification. The new F4 verifier uses those dimensions as dependency
regressions; it does not test every F2 triangulation or accept F2 wholesale.
The exact frozen C1 six-vertex graph, blocks, and 0->1->1->1->2 path are
included. C3 is a separate dependency. Neither C3 nor F2 formal acceptance,
nor F3 recognition, I3 incidence/quotient compatibility, or whole-program
acceptance follows from F4-local P+C+X success.

The general restriction-species CULF mechanism is established infrastructure,
not a novelty claim. The specific work here is the explicit proof on the
original typed cut carriers, its correctly distinct homotopy interpretation,
and the coherent failing-lift controls. Fixed-endpoint quotient/kernel lifting
is a different theorem and is not used as a substitute.

## Original F4 clause preserved verbatim

The following is copied from the unchanged full original contract. Its
historical OPEN label is retained; present review status is stated separately.

### F4 CULF and nonidentifiability

**Class and claim:** M. State and test the appropriate unique-lifting condition for a simplicial map, and prove that it does not imply recovery of the underlying whole or witness from its image.

**Inputs:** F2 and the map forgetting graph edges while retaining the underlying ordered vertex set, partition, and interface data.

**Artifact:** An all-degree proof that the designated forgetful map is CULF, formulated by the relevant cartesian naturality squares, together with an explicit noninjective map on whole objects. State the direction of every map. Explain that the lift is unique after fixing the source whole; it does not identify that whole from its image.

**Discharge:** P and C; X for the nonidentifiability example. Separately test a map that fails unique lifting. The report may not use CULF as a synonym for faithfulness, injectivity, reconstruction, or observational identifiability.

**Tests:** Two graphs with the same ordered vertices and different edges; a fixed graph and a prescribed partition having a unique lifted cut; and a deliberately duplicated cut-witness model that violates the lifting condition.

**Dependencies:** C3, F2. **Status:** OPEN.

**Minimum passing floor:** Prove the actual all-degree lifting condition, nonidentifiability, and a failing-lift control on the selected witness maps. A discrete two-point-to-point example is only a regression check, not the CULF/quotient analysis required by F3/I3.

## Source identities

These complete dependency files are bundled byte-for-byte. Their historical
source-level status and references are preserved, not silently updated.

- Original_Completion_Contract_v0.1_VERBATIM.md
  SHA-256: 47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e
- C1_Model_Theorem.md
  SHA-256: 8a05992fe26c456ed1a5c61c5512e7939ed625da76263b58f61940e1a3a0cd7c
- Global_Cut_Repair.md
  SHA-256: 2329adbd1844a9a62bfefe2094526d490c302acc639116a062590dd2d31ca449

The delivered F4 proof normalizes dependency paths for this portable package;
its mathematical content is unchanged. MANIFEST.json identifies its delivered
bytes and records the original author-source hash separately.
