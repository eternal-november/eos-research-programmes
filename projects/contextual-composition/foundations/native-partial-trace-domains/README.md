# Native partial-trace domains

## Audit and scope

The results concern instantaneous diagonal matching on finite loop interfaces in the native finite-measure graded-writer bicategory. They do not describe repeated execution, eventual termination, recursion, infinite feedback, arbitrary polynomial content, or a free completion. Full raw witnesses (including zero-weight points), actual coefficient arrows, full global writer grades, and unused labels remain part of the interface.

The manuscript passed an independent adversarial review and exact finite rational diagnostics. This is a bounded review record, not a novelty or machine-verified proof claim. No TeX compilation is claimed. The canonical native coherence is inherited from the stated ambient trace; ordinary partial-trace axioms can additionally be read on native-isomorphism classes without replacing the native interface by a semantic quotient.

## Sources and reading route

1. [Finite-measure native feedback](../finite-measure-native-feedback/Finite_Measure_Native_Feedback.tex), Git blob `51517c496be9ed6a31c1faa96ae82a95fbe98171`. Construction is over Set with finite endpoint objects, not over FinSet; raw witness sets may be infinite, with finitely supported measures.
2. Malherbe, Scott and Selinger, *Partially traced categories*, arXiv:1107.3608v2 (4 April 2012), Definition 3.1, Definition 3.2, Remarks 3.5–3.6. [Primary author-hosted PDF](https://www.mathstat.dal.ca/~selinger/papers/ptrace.pdf). The definition uses directed naturality and strength, bidirectional dinaturality, and vanishing-II conditional on the inner trace being defined. Stronger unqualified domain equivalences are not silently substituted.
3. `Partial_Trace_Domains_and_Shared_Coupling.tex`: domain theorem, staged-elimination calculus, sharp coupling bounds, and native projection criterion.

## Results and their interface

For a normalized process, let c(a,u) be the probability of matching the loop input u at external input a. Ambient trace is normalized exactly when z(a) = sum_u c(a,u) = 1 for every a. This maximal normalized restriction of the specified ambient trace satisfies the selected standard partial-trace package. Fixed-loop native cells preserve its domain and induce actual traced cells. Input restriction may remove bad rows, so reverse definedness naturality is false in general, without contradicting the selected standard.

For several loop coordinates, each prospective partial elimination has an explicit remaining-row mass test. A staged elimination is admitted exactly when every prefix passes. Admissible coordinate subsets need not be downward closed: the manuscript gives a deterministic two-bit process whose joint closure is normalized although neither one-coordinate elimination is normalized. Admitted plans with the same terminal eliminated coordinates have canonically isomorphic native results.

For individually traceable components, fix an external input tuple and allow arbitrary independently chosen raw-marginal couplings at each loop-input tuple. Sharp Frechet bounds give the entire attainable interval of joint closed mass. Every coupling is normalized exactly when at most one component coincidence profile is non-Dirac. This conclusion depends on the declared rowwise coupling interface, not on a globally constrained shared seed model.

Normalization alone does not preserve component native projections. With affine coefficient and writer categories, or supplied actual coefficient projection arrows, equation (P) gives exact closed raw-atom marginal constraints. Every coupling is both normalized and projection-preserving exactly when either all coincidence profiles are Dirac, or exactly one is non-Dirac and every other component's raw law at its unique closed input is Dirac. Zero-weight ghosts remain. The manuscript separates fixed-loop trace functoriality from these loop-changing product-projection squares.

These are normalization and native-comparison results for finite diagonal feedback. They do not establish the missing variable-arity polynomial crossing or routing compiler.

## Diagnostics

From this directory:

```sh
python check_partial_trace_domains.py
```

The checked record contains 576 exact rational coincidence-profile cases, 4352 exact raw-marginal cases, the joint-only elimination witness, the normalized-but-distorted native marginal witness, and TeX environment nesting. Finite enumeration supplements the written proofs; it does not establish their unrestricted quantifiers.

