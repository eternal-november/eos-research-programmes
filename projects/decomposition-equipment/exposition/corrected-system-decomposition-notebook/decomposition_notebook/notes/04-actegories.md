# 04 — Actegories separate operator algebra from carrier semantics

**Origin:** chat L2–382, L386–440, L518–588, L2441–2488. **Status:** definition retained; application claims corrected.

## Mathematical core

A left action of a monoidal category \((\mathcal V,\otimes,I)\) on a category \(\mathcal C\) is a functor

\[
\odot:\mathcal V\times\mathcal C\longrightarrow\mathcal C
\]

with coherent natural isomorphisms \((v\otimes w)\odot c\cong v\odot(w\odot c)\) and \(I\odot c\cong c\). Equivalent data can be expressed as a **strong monoidal** functor \(\mathcal V\to\operatorname{End}(\mathcal C)\), where endofunctors compose. The functor acts on *arrows*, too. An actegory is a categorical action; it is only analogous to an ordinary module unless additive/distributive structures are also supplied. See [Capucci–Gavranović](https://arxiv.org/abs/2203.16351).

### Three common look-alikes

- A time **monoid acting on one state object**, \(\phi_{t+s}=\phi_t\phi_s\), is not by itself an actegory on a category of dynamical systems.
- A **parameterized family of laws** \(f_\lambda\) need not have any algebra of parameter composition.
- A **graded monad** is ordinarily described using lax monoidal structure; its grade-composition maps need not be isomorphisms. It is not automatically an actegory.

## Multiple actions are not independent by default

Actions of \(\mathcal V\) and \(\mathcal W\) on the same \(\mathcal C\) may commute up to coherent interchange, interact through distributive or semidirect-type data, or fail to admit a joint action. Interchange is *extra structure*. A bare notation such as \(\mathcal V,\mathcal W\curvearrowright\mathcal C\) does not construct it.

**Witness.** On \(\mathbb R^2\), take \(V=\partial_x\) and \(W=x\partial_y\). Their flows are \(\Phi_t^V(x,y)=(x+t,y)\) and \(\Phi_s^W(x,y)=(x,y+sx)\). Applying them in opposite orders changes \(y\) by \(st\). “Independent operator kind” does not imply commuting dynamics.

## Restriction-preserving actions cannot freely alter definedness

For a restriction functor \(F\), \(F(\bar f)=\overline{Ff}\). If \(f\) is total, then

\[
\overline{Ff}=F(\bar f)=F(1)=1.
\]

Therefore a restriction-preserving functor preserves total maps. On a fixed carrier, this mechanism cannot create new partiality from a total arrow. If changing laws is intended to make previously valid inputs invalid, the semantics must allow such variation explicitly through another typed construction. This is an obstruction to a proposal in chat L2441–2488, not an objection to actegories themselves.

## Selection criterion

Use an actegory when the operator family *already has a coherent composition algebra* and its members transform both systems and relevant system maps. Do not choose it solely because operators and states can be described separately. Lifting adjunctions, monads, constraints, or contracts requires additional compatibility arguments.

**Related notes:** [03](03-types-of-physical-law.md), [06](06-indexing-institutions-doctrines.md), [08](08-restriction-categories.md).
