# 15 — Weil functors, jets, Cartan distributions, and the variational bicomplex

**Origin:** chat L929–935, L1114–1175, L948–971. **Status:** underexplained candidates developed as an organized mathematical note; some content is external expansion.

The shared theme is **separating finite-order differential information, differential equations, and actual solutions**. These constructions are related, but are not one interchangeable “infinitesimal dynamics” framework.

## Weil algebras and functors

A Weil algebra \(A\) over \(\mathbb R\) is a finite-dimensional commutative local \(\mathbb R\)-algebra with residue field \(\mathbb R\) and a nilpotent maximal ideal. The canonical example is the dual numbers

\[
A=\mathbb R[\varepsilon]/(\varepsilon^2).
\]

On a suitable manifold category the corresponding Weil functor \(T^A\) produces \(T^A M\), a space of \(A\)-infinitesimal points; for dual numbers, \(T^A M\cong TM\). Crucially,

\[
T^A\circ T^B\cong T^{A\otimes B}
\]

under the standard hypotheses. This gives a genuine functorial **operator algebra of infinitesimal probes**, and is an interesting connection to actegories not developed in the chat. It does *not* create a vector field, law of motion, or flow on \(M\). The heuristic \(M^A\) is internal-point notation in suitable geometry, **not** ordinary set-theoretic exponentiation of a manifold by an algebra. [Kriegl–Michor](https://www.mat.univie.ac.at/~michor/kmsbookh.pdf).

## Jet bundles: finite derivative data of sections

For a configuration bundle \(\pi:E\to M\), \(J^kE\) records \(k\)-jets of local sections: their derivatives through order \(k\), identified at each base point. A differential equation can be represented as a submanifold or, more generally, a subset/subspace \(\mathcal E\subseteq J^kE\) with specified regularity. A section \(s\) is a solution when its prolongation \(j^ks\) lies in \(\mathcal E\).

This separates **equation locus** from **holonomic solution**. A point satisfying the equation in jet space is not automatically the jet of a global solution satisfying boundary data. Prolongation and integrability/compatibility conditions matter.

## Cartan distribution and diffieties

Jet bundles carry **contact geometry** distinguishing legitimate jets of sections from arbitrary motions in jet coordinates. On infinite jets, the Cartan distribution is spanned locally by total-derivative operators; it encodes the infinitesimal directions tangent to prolonged solution graphs. A **diffiety** is a geometric formalism for a suitably regular/involutive infinite prolongation of a PDE system. No ordinary finite-dimensional vector field is guaranteed.

## Variational bicomplex

On \(J^\infty E\), differential forms admit a horizontal/vertical bigrading, with

\[
d=d_H+d_V,
\qquad d_H^2=d_V^2=d_Hd_V+d_Vd_H=0.
\]

This organizes total derivatives, variation, Euler–Lagrange operators, boundary terms, and (under suitable hypotheses) conservation laws. It is especially useful when asking whether a differential equation is variational, how a current depends on a Lagrangian, or which terms are exact/boundary contributions. It does **not** make every PDE an Euler–Lagrange equation. [Ian Anderson, *The Variational Bicomplex*](https://ncatlab.org/nlab/files/AndersonVariationalBicomplex.pdf).

## Selection rule

Use Weil functors for *functorial infinitesimal probes*; jets for *differential laws as constraints on derivatives*; Cartan geometry for *holonomicity and prolongation*; and the variational bicomplex for *variation, boundary terms, and conservation identities*. These constructions may interoperate but do not determine dynamics without an equation, boundary conditions, and a solution notion.

**Related notes:** [03](03-types-of-physical-law.md), [12](12-sheaves-and-stacks.md), [16](16-dirac-and-implicit-physical-systems.md).
