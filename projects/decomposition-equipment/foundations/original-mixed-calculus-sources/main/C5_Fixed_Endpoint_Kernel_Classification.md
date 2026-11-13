# Actual C5 fixed-endpoint lifting: a sharp kernel classification

Author proof candidate, 29 October 2026. This is a supporting theorem, NOT the full requested original-to-equipment presentation bridge.

## Plain-language abstract

A quotient can make a refinement appear possible even though no actual refinement connects the specified endpoints. In the original graph-cut calculus this issue is especially rigid. If a quotient identifies two different ordered vertex partitions, it necessarily invents such a refinement. In the natural family of quotients that retain partitions and forget only scalar labels according to the whole graph, we can classify exactly which quotients avoid this problem. They may forget multiplication by one fixed subgroup of invertible scalars on every nonempty graph, and may forget nothing on empty graphs. The empty case is forced by genuine nullary operations, not a technical convention. These quotients continue to work under arbitrary noninvertible interface restrictions in the concrete graph-span equipment, but they do not remove its separate cut-transport obstruction.

## 1. Actual source and scope

Use `research/workstream_A/rewrite/A3_LOCAL_COMPARISON.md`, sections 1–6, in the recovered original source. Original generators are binary cuts C, nullary U_A, and unary D(W,m). Its seven equations are R, UL, UR, D0, DA, DL, DR. They are NOT the seven equations of `Extended_Local_Presentation.md`.

The proved original normal form identifies an operation with the complete output (G,f), complete ordered input path, ordered actual partition pi=(U_i), and scalar m in a commutative monoid M. Nullary operations exist exactly on (empty,id_A), and have every scalar m. Substitution retains the whole, replaces each U_i by its actual ordered subpartition, and multiplies outer and child scalars.

We use the fixed-endpoint lifting requirement (FL): for every actual outer operation a and every fully specified replacement-profile skeleton, if a forest u has quotient composite equal to a specified actual target b, there exists a forest v in the SAME quotient class as u with a[v]=b literally. Occurrences and all profiles stay fixed. A nullary outer operation has one empty forest, not an adjustable scalar at a nonexistent child.

## 2. Partition rigidity, without a scalar-kernel hypothesis

**Proposition 1.** Any parallel substitution congruence satisfying FL on all actual original C5 operations identifies no pair with different ordered partitions.

**Proof.** Suppose a~b are parallel and have different partitions. At every input occurrence of a choose the identity unary refinement with that same input component as its one-leaf replacement profile. The quotient identity forest gives a refinement from [a] to [b]. Every actual forest with this skeleton is unary at each occurrence. A unary graph cut has the sole block equal to the entire child vertex set, so substituting any such forest into a retains a's ordered partition exactly. It cannot give b. For a nullary profile there is only the unique empty partition anyway. This contradicts FL. QED.

This obstruction is specifically about retaining specified original outer and target witnesses. Allowing the outer endpoint to move within its class changes the problem and avoids this argument; that is not fixed-endpoint recovery.

## 3. Graph-indexed scalar kernels

Consider relations R_G on M, one per ordered graph G, and the candidate relation

    (pi,m) ~ (pi',n) iff pi=pi' and m R_G n

on each complete parallel operation fibre with output graph G. The relation is independent of interface arrows and profile except for this graph parameter. This is an explicitly delimited family, not a classification of all C5 congruences.

**Lemma 2 (actual generator criterion).** This is a substitution congruence iff:

1. each R_G is a monoid congruence;
2. R_(G|U) is contained in R_G for every actual vertex subset U.

**Proof.** Unary D composition gives multiplication compatibility. Necessity of induced inclusion uses the binary generator with partition (U,U-complement), both interface grades identities, and scalar-one other child and outer cell. Changing the U-child scalar propagates its equation to the output G. Sufficiency follows directly from the flat substitution formula: outer changes use R_G's multiplication compatibility; child changes first use induced inclusion and then that same compatibility. This covers empty U, nullary children, and arbitrarily many occurrences. The seven original equations ensure the formula is the actual presentation quotient, not an independent assumed semantics. QED.

For N>=1 all graphs on <=N vertices occur. Fix any object of the nonempty category K for the identity-grade instances below.

**Theorem 3 (classification).** Within the family of Lemma 2, FL for every original operation and skeleton holds iff there is a subgroup H of the unit group M^× such that

    R_empty = equality,
    m R_G n iff n=mh for some h in H, whenever G is nonempty.

The same subgroup H works for every nonempty ordered graph; no graph-dependent choice survives the full lifting requirement.

**Necessity.** A nullary outer operation of scalar m has only the empty forest. If m R_empty n, FL would require its unchanged composite m to equal n. Therefore R_empty is equality.

Let P be the one-vertex graph and H=[1]_(R_P). Monoid congruence makes H a submonoid. For h in H take the unary outer D(P,h), its identity child, and actual target D(P,1). They are equal in the quotient. FL gives a unary child of scalar k in H with hk=1. Commutativity makes h a unit and k its inverse; thus H is a subgroup of M^×.

For any nonempty G on r vertices, take the actual ordered singleton partition (in vertex order), identity grades, outer scalar m, and identity forest. If n R_G m, FL supplies r singleton children, each scalar h_i in H, with n=m product_i h_i. Hence [m]_(R_G) is contained in mH. Conversely the induced-subgraph inclusion R_P subset R_G and multiplication compatibility imply mh R_G m for all h in H. Thus [m]_(R_G)=mH. This also proves the statement for P and does not require cancellation of arbitrary M elements. QED.

**Sufficiency.** Lemma 2 holds because H-orbit equivalence is a monoid congruence and equality on empty graphs is contained in it. Fix a,u,b satisfying the quotient refinement equation. Partitions coincide exactly. If the output graph is empty, every input graph is empty, and all scalar classes are singleton, so the actual equation already holds. If G is nonempty, at least one input occurrence has a nonempty vertex block. Write the composite scalar as s; the target scalar is sh for some h in H. Multiply the scalar of the chosen nonempty child by h, leaving every block, grade, profile and other scalar unchanged. This child remains in its quotient class and its modified forest composites exactly to b. If the outer arity is zero then G is empty, already handled. QED.

The proof works for infinite commutative monoids too; finiteness only makes the subgroup table and fixed-parameter presentation finite.

## 4. Explicit equations and normal forms

For a chosen H impose, for every nonempty component W and h in H,

    D(W,h)(x_W) = x_W.

Do NOT impose these equations at empty graph components. Together with the original seven relations, these generate exactly the classified kernel. Soundness follows from Lemma 2. For completeness, if n=mh then D(W,mh)=D(W,m)D(W,h)=D(W,m) by DA, and composing at the output of any scalar-one cut gives the arbitrary profile instance. The original DL/DR equations identify placement of scalars, including inside arbitrary binary trees; R,UL,UR provide its original complete flat normal form. Empty components remain scalar-exact because the proposed kernel is a separating model of all added equations. This is generation from original actual rules, not declaration of all semantic equalities.

If M has no nontrivial units, the only member of this family satisfying FL is equality. In particular arbitrary idempotent or absorbing-scalar collapse does not pass merely because multiplication respects the quotient.

## 5. Noninvertible restrictions in the concrete equipment extension

In the existing concrete graph-span equipment, a cell is (pi,phi,m). Extend the relation by retaining pi and the ACTUAL coefficient map phi, quotienting m by H only when the output graph is nonempty. This is generated in the larger signature by D(H,h)=id_H for EVERY concrete nonempty horizontal H, not merely the embedded original components W. This is not a claim that the original equations generate every such new-horizontal equation in the free envelope. Its substitution congruence follows from the same induced-block argument. Chosen restriction-factorization and contextual-unit bijections preserve graph and scalar and transform phi bijectively, so both directions respect this relation for arbitrary interface maps, including noninjective and nonsurjective maps.

Freeze the full substitution vertical-map family u_0,...,u_k, including its sole u_0 when k=0, along with the complete replacement profiles. The FL proof remains valid there: quotient equality retains the exact composed coefficient map, and adjusting a child scalar does not change any boundary matching or coefficient. A nonempty output still has at least one nonempty graph input. When output is empty all scalar and coefficient data are retained. Hence no coefficient lifting is being assumed to solve a scalar adjustment.

This statement is about the concrete extension. It does NOT assert every extended horizontal or coefficient map is generated by the original C5 signature; that is the separate generation bridge under investigation.

## 6. What this does not repair

The coefficient comparison for a noninjective interface change can still fail to be a bijection, and nullary comparison can still be the nonbijective diagonal A'→A'×_A A'. Our scalar quotient deliberately retains coefficient maps, so it cannot turn that failure into invertibility. Thus the theorem is an exact original-kernel classification and a restriction-stable positive family, not a solution to strict all-interface cut transport.

The classification is also not a novelty claim about scalar decorations: it establishes the program's precise fixed-endpoint constraint using the original calculus and its nullary cases. Its main structural message is negative: nontrivial partition quotienting is incompatible with universal fixed-endpoint lifting, while the remaining graph-indexed scalar freedom is much smaller than arbitrary graph-activated forgetting.
