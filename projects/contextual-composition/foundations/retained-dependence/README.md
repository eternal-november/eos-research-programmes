# Retained dependence: admission, wiring, and temporal substitution

This tranche separates the general construction from its semantic realizations. It is not a completed concurrent interactad or a novelty claim.

## Main mathematical route

1. **Local admission.** `Tree_Overlap_Admission_and_Retained_Reassociation.tex` derives a joint effect from matching overlap effects on a finite tree, for any Set functor weakly preserving pullbacks. Arbitrary maps and actual raw compatible tuples are retained.
2. **Native wiring.** `Multicategorical_Coupling_Wiring_and_Context_Interchange.tex` records chosen joint contexts and native projections in the standard cone multicategory. Its additional context theorem proves that dependent serial composition commutes with hierarchical projection substitution.
3. **Temporal assembly.** `Native_Coupling_Cones_and_Conditional_Assembly.tex` proves that local conditional native squares imply full assembled native squares, including actual body states. A conditional component law must factor through its declared component input, not merely match after averaging over hidden joint state.
4. **Why dependence must remain data.** `Naturality_Obstruction_to_Marginal_Only_Dependence.tex` proves that a natural marginal-only coupling operation for finite distributions is necessarily independent. Cone representability also fails in the relevant deterministic-map effect categories: all dependence witnesses cannot be replaced by a universal product.

The admission theorem constructs the existence of root objects; the cone calculus retains their chosen dependence and derives composition laws. These are complementary steps, not an assumption that a desired global coupling was given in advance.

## Important boundaries

- Reassociation of nested effects is a bijection only on **fixed canonical compatible-tuple carriers**. Redundant witness presentations and conditional disintegrations are not covered by that bijection.
- No natural or associative choice of coupling is supplied. Different choices remain different.
- Finite-tree consistency does not solve arbitrary cyclic overlap constraints.
- Finite distributions and nonempty powerset are separate instantiations, not definitions of the theory.
- Raw zero-weight or disallowed witnesses remain distinct from effect support. Effect preservation does not imply raw surjectivity.
- Guarded finite-prefix compatibility does not create an infinite effect, fairness theorem, or total trace.
- The weak-pullback and elementary multicategory machinery are established foundations; the contribution being tested is their exact native context/body integration.

## Diagnostic

Run `python3 check_tree_retention.py`. It checks a finite rational four-component case through five bracketings, zero-weight tuples, the cyclic inconsistency boundary, and why redundant witnesses must be excluded. These diagnostics are not a formal certification of the general proofs.

## Connection to the existing native theory

The context categories and dependent bind used here are those of the [effect-fibre interaction construction](../occurrence-effect-interaction/README.md). The new layer retains joint contexts and their native projections instead of replacing dependence by independent products. Its conditional assembly theorem derives composite native squares from the local squares. The elementary cone multicategory and weak-pullback/tree-gluing facts are background machinery, not claimed innovations.

This does not supply a new independent content crossing or all the laws of a concurrent interactad. Conditional continuation squares and actual bodies remain premises. Arbitrary cyclic wiring, coherent feedback beyond the scoped retained-prefix result, and comparison of redundant joint presentations remain separate obligations.

## Verification

The written proofs were independently reviewed, including arbitrary-map admission, the native conditional factorization, cone orientation, fixed-carrier reassociation, and the boundary between raw witnesses and their effects. This is not mechanized certification. TeX compilation is unnecessary. Verify the frozen files with `sha256sum -c MANIFEST.sha256` and run the finite diagnostic above.
