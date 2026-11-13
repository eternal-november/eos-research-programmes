# 17 — Groupoids, stacks, and derived solution spaces: do not erase witnesses too early

**Origin:** chat L934–935, L948–971 and related stack mentions. **Status:** an elaboration of a short source-list entry; research candidate, not a concluded architecture.

The decomposition question here is *what a space of solutions forgets when it is reduced to a set of equivalence classes*. In gauge theories and singular constraint problems, two forms of information may matter even after the ordinary solution set has been computed:

1. **Automorphisms/equivalence witnesses:** how solutions are related and what stabilizers remain.
2. **Nontransversality and infinitesimal obstruction data:** why a solution may be singular or fail to deform smoothly with a parameter.

## Groupoids and stacks: equivalence is structured data

If a group \(G\) acts on a space \(X\), the orbit set \(X/G\) identifies equivalent elements but discards stabilizer data. The **action groupoid** retains objects \(x\in X\) and arrows \(x\xrightarrow{g}gx\). A quotient stack \([X/G]\) (in a suitable geometric category/site) retains this groupoid-like moduli information and descent under changes of local presentation.

For instance, two orbits may each become one point in an ordinary quotient even though the corresponding stabilizer groups differ. Such a collapse is unacceptable if the consumer asks about residual gauge symmetries or local deformation types. It may be harmless if the only question is the value of a gauge-invariant scalar observable.

## Derived intersections: preserve hidden constraint geometry

Classical simultaneous constraints often form an intersection \(Z(f)\) or critical locus \(\{\mathrm dS=0\}\). If constraints meet nontransversely, the ordinary set or scheme can suppress higher intersection/deformation information. **Derived** intersections and derived critical loci retain additional homotopical/algebraic structure; tangent–obstruction complexes can indicate singular infinitesimal behavior. A sharper example uses **redundant constraints** \(f:\mathbb A^1\to\mathbb A^2\), \(f(x)=(x,x)\). The classical scheme-theoretic zero locus is the reduced point \(x=0\) because the ideal \((x,x)=(x)\). The *derived* zero locus retains a degree-\(-1\) Koszul homology class: for the Koszul complex of \((x,x)\), the cycle \((1,-1)\) is not a boundary over \(\mathbb R[x]\), while its multiple by \(x\) is. Hence \(H^{-1}\cong\mathbb R[x]/(x)\). The redundant-equation obstruction is invisible to the ordinary scheme, not merely to its underlying set.

This does not automatically yield a physical stability estimate, a numerical solver, or global existence. A derived tangent or obstruction complex is **algebraic infinitesimal information**. Analytic dynamics require separate regularity, topology, or PDE analysis.

## Relation to law variation

A parameterized family of laws may change not just the number of solutions but their stabilizers, multiplicities, and singularity types. A model indexed only by solution sets cannot detect all such changes. Stacks/derived geometry become appropriate when the downstream question *actually consumes* those distinctions.

**Diagnostic:** before adopting higher geometry, state the missing datum that the ordinary quotient loses and give a consumer that requires it. Without such a consumer, the additional machinery is overhead rather than demonstrated adequacy.

**Related notes:** [02](02-preservation-and-substitutability.md), [12](12-sheaves-and-stacks.md), [15](15-weil-jets-and-pde-geometry.md).
