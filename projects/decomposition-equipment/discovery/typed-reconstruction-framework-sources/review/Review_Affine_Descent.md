# Independent review of the unit-affine positive application

29 October 2026. Non-author AI proof review, not Lean verification or external human review.

## Verdict

The corrected affine model supports a genuine unbounded positive application of the typed-cover theorem. It proves coherent reconstruction for arbitrarily many overlapping intervals on one retained ordered frontier, with induced internal coordinate changes and actual fixed-endpoint refinement lifts. This is stronger evidence than the path-only calibration. It remains a structured affine application, not an original C5/I4 discharge or an arbitrary nonplanar crossing theorem.

Reviewed source: `main/Affine_Descent_Model.md`, final SHA256 `b82a72d76b427cc8c41a069ef8ade80a935c345536beb75379ca843c4a3aabdd`. The review identified one false unit-normalization sentence and two potential overstatements; these were corrected. No further mathematical blocker was found.

## Independent reconstruction

1. **Assembly and presentation.** The substitution formula is associative because both coefficient multiplication and the accumulated affine constant expand identically. Positive arities preserve invertibility of every coefficient. Structural induction moves translations to the root, distributes scalings and reassociates the ordered sum. Evaluation at zero and standard basis inputs separates the resulting normal forms. This is a complete assembly presentation, not by itself a complete independently specified presentation with cut/transport constructors.

2. **Normalized cuts.** The inner coefficients a_j/a_i reassemble exactly with outer pivot a_i. For a specified planar tree, all nonroot constants zero and all nonroot leading coefficients one force the edge ratios by telescoping along the first-leaf paths. This does not classify all factorizations; arbitrary factors retain internal affine gauges and offset distributions.

3. **Unit defect, corrected.** A newly inserted unary root is generally (b;a_first), not identity. Example over Z/4: f=2+3x+y has normalized full-interval cut outer=2+3z and inner=x+3y. Nonroot unary vertices are identities, but all-degeneracy compatibility is unavailable with this normalization. The corrected text explicitly restricts the claim. This qualification must survive any summary describing cut coherence.

4. **Transport.** Substitution of input coordinates gives h_I(r_j)=t_I h'_I with slope u_i and translation sum(a_j/a_i)v_j. The old outer transported by this t_I has both the new pivot coefficient and the new whole constant. For sequential changes, the new normalized ratios are a_j u_j/(a_i u_i); composing the two internal gauges gives exactly the direct composite translation. Output scaling cancels from inner ratios. The formulas justify coherent gauges rather than an assertion that the internal boundary stays unchanged.

5. **Views and CRT.** Units modulo a divisor lift to units modulo N by prime-power choices. Compatible modular coefficients are units modulo L because every prime dividing L appears in some view. Constants and unit coefficients have respectively N/L and phi(N)/phi(L) lifts. Thus the stated operation-fibre count follows. For the precise abstract-theorem interface, the join of view kernels is equality modulo gcd: CRT constructs an intermediate parameter tuple z matching x modulo one divisor and y modulo the other whenever x,y match modulo the gcd. Unit lifting supplies the needed intermediate unit coefficients. Hence the actual congruence join, not just an arbitrary chosen overlap, is used. Modulus-one overlaps are terminal fibres, as now explicitly stated.

6. **Actual arrows.** Fixing outer and whole forces each inner coefficient to A_i^{-1}B_ij. The quotient equation leaves exactly one linear constraint on inner constants with unit coefficient A_1. Choose m-1 constants in their prescribed classes and solve uniquely for the last. The solution remains in its prescribed residue class. This proves class-image saturation and precisely (N/L)^(m-1) actual arrow witnesses. It uses a joint forest and m>=1; it makes no claim for nullary forests or nonunit coefficients.

7. **No coherent section.** Additive nonsplitting alone would not exclude an affine section, since a translation might lift with a nontrivial slope. The corrected stronger proof is valid: associativity forces the unit coefficients of any binary-addition lift to be one; translation naturality then forces the translation lift's slope to be one; the involution equation contradicts its odd offset modulo4. Thus original arrow lifts do not imply a calculus-homomorphic choice of representatives.

8. **Overlapping interval families.** Collecting endpoints creates one common ordered segmentation, with each original occurrence used once. For each requested interval, grouping its segments with the stated pivot ratios reconstructs its normalized inner factor. The shared segment is the same node across the diagram, not a copied independent choice. Refinement of segmentations telescopes, so insertion order is irrelevant. Gauge translations aggregate to the interval translation; pivot slopes cancel in the transported grouping coefficients. This establishes finite nonlaminar interval-family coherence. It does not equate row-major and column-major profiles or solve unknown-frontier reconstruction.

## Computation

Re-ran the author checker after corrections: **78,114 exact checks PASS**, including sampled formula checks with fixed seed and exhaustive parameter subchecks. These are not all exhaustive across the whole tested range; the report should retain that distinction.

Wrote an independent checker `review/check_affine_review.py` and saved its output in `review/check_affine_review.json`. It verifies:

- all 32 candidate lifts of binary addition and translation fail the three necessary equations for an affine-calculus section Z/2→Z/4;
- the explicit root-unary normalization counterexample;
- all **24,576** two-input Z/4 cut/transport cases with every unit slope, offset, and nonempty interval.

These support the symbolic proof and its boundary corrections. They do not establish unbounded claims without the written induction and identities.

## Acceptance boundary

Accept this as a concrete unbounded, graph-independent positive application of the conditional framework tools, with meaningful actual-arrow and shared-interval data. Do not describe it as full unique factorization, ordinary 2-Segal coherence, all-degeneracy-compatible normalized cuts, arbitrary interface restriction, nonparallel crossing, architecture discovery, or completion of original C5/F3/I4/I5. The contribution is its explicitly verified integration; affine algebra, CRT and interval segmentation are standard mechanisms and do not by themselves establish novelty.

Final source-alignment pass (29 October 2026, 02:36 UTC): the actual congruence-join/gcd and intersection/lcm bridge is now explicit in §5 and is correct. The author checker was rerun after addition of 35,360 exhaustive scalar/unit parameter join/meet checks at N=12 and N=24; total 78,114 PASS. The final report, `Typed reconstruction framework results.txt`, was read in full and accurately preserves the reviewed theorem scopes, root-unit correction, actual-arrow distinction, finite-test limitations, and open original-contract bridge. No placeholder or unsupported completion claim was found.
