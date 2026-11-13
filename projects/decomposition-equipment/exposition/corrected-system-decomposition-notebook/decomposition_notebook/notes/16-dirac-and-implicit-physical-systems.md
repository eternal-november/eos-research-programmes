# 16 — Dirac structures and Tulczyjew triples: constraints, energy, and dynamics

**Origin:** chat L936–938, L948–958, L465–488. **Status:** external technical expansion of source-listed techniques; not a universal open-system prescription.

These are strong examples of **representation by constrained relations** rather than arbitrary explicit state updates. Their value is particularly high when physical interfaces carry energy.

## Linear Dirac structure: a power-conserving relation

Let \(V\) be a finite-dimensional real vector space. Equip \(V\oplus V^*\) with the symmetric bilinear form

\[
\langle(v,\alpha),(w,\beta)\rangle=\alpha(w)+\beta(v).
\]

A **linear Dirac structure** \(D\subseteq V\oplus V^*\) is maximally isotropic under this pairing (equivalently \(D=D^\perp\)). Therefore, for every \((f,e)\in D\), \(e(f)=0\): this gives an abstract power-conservation identity for conjugate flow/effort variables. For smooth manifolds, one ordinarily also requires suitable involutivity under the Courant bracket for an **integrable** Dirac structure. A merely maximally isotropic subbundle is sometimes called an *almost Dirac* structure.

The Dirac structure alone is **not** a complete dynamical system. It provides an interconnection/constraint geometry. An energy function \(H\), storage flow, dissipation law, inputs, and boundary conditions select evolution. A typical port-Hamiltonian relation is

\[
(-\dot x,\mathrm d H(x),f_{\mathrm p},e_{\mathrm p})\in D,
\]

with sign conventions chosen for the storage port. Appropriate power balance follows from isotropy; dissipation and passivity require additional elements/inequalities. Power conservation is not reversibility, existence, uniqueness, or asymptotic stability.

For particular well-posed interconnection classes, composing Dirac structures preserves an energy-compatible port-Hamiltonian model; those are substantive compositional results rather than a generic consequence of any wiring. [Van der Schaft, overview](https://doi.org/10.4171/022-3/65); [interconnection theorem](https://www.sciencedirect.com/science/article/pii/S0005109806003682).

## Tulczyjew triple: relate Lagrangian and Hamiltonian presentations

For a configuration manifold \(Q\), the triple exploits canonical maps between

\[
T^*(TQ),\qquad T(T^*Q),\qquad T^*(T^*Q).
\]

One canonical map \(\alpha_Q:TT^*Q\to T^*TQ\) and the symplectic identification \(\beta_Q:TT^*Q\to T^*T^*Q\) allow dynamics to be encoded as submanifolds/relations. For smooth \(L:TQ\to\mathbb R\) and \(H:T^*Q\to\mathbb R\), representative dynamics are

\[
D_L=\alpha_Q^{-1}(\mathrm d L(TQ)),
\qquad
D_H=\beta_Q^{-1}(\mathrm d H(T^*Q)),
\]

with a fixed sign convention for \(\beta_Q\). When a Legendre transform is regular, these presentations can correspond. For singular Lagrangians there may be primary constraints, gauge freedom, or no unique Hamiltonian vector field, so “same physics in both forms” is not automatic. [Grabowska–Grabowski](https://www.aimsciences.org/article/doi/10.3934/jgm.2013.5.445).

## How the decompositions differ

**Dirac:** split energy storage, port power-conservation/interconnection, and admissible flows. **Tulczyjew:** relate variational and cotangent-bundle dynamical presentations without committing prematurely to an explicit evolution vector field. **Courant algebroid:** an ambient bracket/pairing/anchor structure in which geometric Dirac structures can be defined and studied.

These do not solve the general “vary every physical law freely” problem: the geometric substrate, energy variables, and compatibility of interconnections impose real constraints.

**Related notes:** [03](03-types-of-physical-law.md), [10](10-relations-allegories-and-effects.md), [15](15-weil-jets-and-pde-geometry.md).
