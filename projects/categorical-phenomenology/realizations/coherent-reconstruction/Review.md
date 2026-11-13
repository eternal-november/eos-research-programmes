# Independent proof review

Reviewed 3 November 2026. This review is bound to the exact `report.tex` source with SHA-256:

```text
a6a4730c4d9f48a02c1c292b8f3aacfe3844c0482ae3f1aa7891645368e29d5c
```

## Verdict

**No unresolved mathematical blocker found within the report's stated finite, statewise, witness-retaining scope.** The compatibility, resource, initiality, and transport claims are supported by the displayed constructions and proofs. This is a skeptical mathematical review, not formal verification, novelty clearance, or certification of a broader stochastic-process theorem.

The review read the prior report, source audit, obstruction notes, derivation notes, and final report. It independently reconstructed the main factorization and posterior arguments. The author was notified of issues during drafting; the final source incorporates the necessary scope clarifications below. The reviewer did not edit the author's source.

## Proof checks

1. **Linear compatibility really preserves statewise rows.** Equation `eq:Zrow` is imposed separately for every announcement/hidden-tuple pair, not merely after aggregation. For positive `alpha[j,h]`, division yields a row in the prescribed coupling polytope. Conversely every native implementation yields these equations by summing states with the same deterministic tuple. The split construction therefore preserves the fixed continuation rows, rather than only the local products or output laws. Zero-mass pairs are safely omitted. Compactness and the rational-feasibility statement are valid.

2. **No uncounted announcement memory.** The reconstruction's middle states are the positive `(j,h)` pairs. Its cost explicitly counts every duplicate occurrence of a tuple. The correlation family proves that splitting can be necessary: the displayed minor has determinant `(1-epsilon)^(m-1)/m^(2m)`, giving the matching lower bound `m` even with strictly positive conditional joint outcomes.

3. **The restricted-rank formula is exact for the declared class.** Partitioning a realization by its deterministic tuple gives one factorization with continuation rows in each `K_h`. Concatenating least such factorizations gives a realization with the claimed sum of ranks. The existence of a global minimum follows from a nonempty finite range of attained integer costs, not an unjustified continuity assertion. This is not ordinary nonnegative rank in general and is not an efficient optimizer. The zero-block convention is consistent even for empty row polytopes.

4. **The arbitrary-generator lower bound has the necessary hypotheses.** The explicit commuting retained-link squares are essential. Under those squares, strong comparisons, nonnegative normalized kernels, and disjoint time-homogeneous phases, reachable middle states yield the required `A`, stochastic `B`, and deterministic tuple map. The three reached phase supports are disjoint, supplying the two additional states. Strong comparisons to observable local generators alone do not imply the retained-row squares; the report correctly excludes that weaker class.

5. **The tensor functor and initiality hold.** Type preservation prevents a native arrow from mixing distinct tuples, and `CB'=B` preserves the complete retained kernel. Together with `AC=A'`, these preserve the full tensor. The posterior from `N(Z)` to any object over `Z` is normalized and forced entrywise by the root equation and type preservation. Unused target states cause no extra freedom: their incoming coefficients are forced to zero. The empty-or-singleton hom-set argument proves the stated fully faithful left adjoint `N` to the discrete tensor functor `P`.

6. **Restriction arrows have the correct direction and compose.** The derived comparison is `N'(F_*Z) -> F(N(Z))`, not the generally invalid deterministic reverse collapse. The formula includes the stochastic announcement channel when present. Zero intermediate masses contribute no undefined divisions. Sequential comparisons agree by initiality, or by summing the intermediate announcement indices and cancelling positive mass factors. The local-model triangle is correctly typed. Rebracketing isomorphisms concern one retained full tensor, not independently chosen completions.

7. **Committed intermediate diagrams are not confused with rebracketing.** The simultaneous test includes all chosen objects and their deterministic hidden and coarse maps through the explicit carriers `E_A` and `S_A`. Its forward direction assumes an actual joint retained link supported on that carrier; it does not invent such a link from unrelated stochastic marginals. Arbitrary stochastic intermediate arrows are outside the stated corollary. These restrictions are substantive and correctly visible.

8. **The row-polytope umbrella is valid with its stronger witness semantics.** Homogenized linear equalities and inequalities characterize each positive conditional row; nonnegative zero rows cause no spurious conditional choice. Linear readouts can be included in the finite-generator separation construction. Full-kernel arrow preservation remains explicit. The fixed-`Q` case is recovered on `Omega=S x I`, including the local retained-state/output pair calculation, so distinct global outputs are not inadvertently identified. The extension does not infer a joint transition witness from separate simulations and links. The sharp fair-bit example demonstrates precisely that gap.

9. **Examples respect the hypotheses.** The shared-profile criterion and unrestricted stochastic-common-source construction are valid in their separately stated scopes. The retained cycle example is explicitly a direct-assembly problem without a supplied joint prior: its inconsistent pair laws cannot pass the main fixed-`w` marginal checks. The singleton-coarse example correctly distinguishes direct joint transition assembly from existence of a common readout on the prescribed product coarse carrier.

## Resolved drafting issues

- Explicit unused-state/non-surjectivity scope was retained.
- Generic transport now derives row-polytope preservation from concrete input squares.
- Intermediate carrier equalities are explicitly restricted to deterministic maps.
- The umbrella keeps the full transition-witness kernel, not merely its separate marginals; its readout map is linear.
- The cycle example no longer risks being read as a fixed-`w` instance passing all preliminary checks.
- A LaTeX split-row escaping defect was corrected.

## Reproducibility checked independently

The reviewer ran `checks/run_checks.sh` after the nine-group update. All nine groups passed; ordinary Python and `python3 -O` produced output byte-identical to `expected_output.txt`. These include randomized interface transport, zero intermediate mass, reverse-direction failure, and the additional transition-witness obstruction.

Checked executable SHA-256:

```text
b0e293d1c34839825211508f58bd9eaf92f71f6f9d805c0a3a04e4adb6c60cce  checks/joint_gluing_checks.py
4397d9c828618e673e5d1359052afea8dfa30399f156d202681de9ebb9903fea  checks/expected_output.txt
1bc4eeb1958a7f588ebacb9cdb8471536a7a75a39f838bbdbfdd37569747a4ab  checks/run_checks.sh
```

The reviewer also checked environment nesting, unique labels, resolved internal references and citation keys, and the corrected line breaks. The source was not compiled and no PDF layout was inspected. The finite regression suite is evidence for its examples and formulas, not a proof by testing of the general theorems.

The final packaging-only change from “source audit and derivation notes ... intermediate calculations” to “source audit and example notes ... exact obstruction calculations” was checked by reversing that single sentence and recovering the previously reviewed source hash `d3ab4665661adbc0bca0c3bfbdb73ab572a23d70975a80250bb4e92f43457a49`. No mathematical changes were present.

## Boundaries that must remain in any summary

This is a finite two-stage synthesis with supplied local factors and explicit support or row-polytope architecture. State count excludes alphabet/table size and sampling cost. It does not establish unrestricted causal-mechanism preservation, arbitrary multistage realization, stochastic intermediate-diagram gluing, discovery of unknown global kernels, or coherent selection of minimum-state binary glues. The mathematical review does not independently certify the bibliography or priority claims; the separate source audit governs those statements.

Any later change to `report.tex` invalidates the exact-source binding above until the changed material is rechecked.
