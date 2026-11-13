# Crossing grid conservative refinement obstruction

## Plain language summary

Two decompositions can reproduce exactly the same whole-system behavior and nevertheless have no common refinement that preserves what each decomposition says at its internal boundary. This is stronger than saying that one obvious refinement algorithm fails.

The example below uses four actual open components arranged in two rows and two columns. Both the row decomposition and the column decomposition are behaviorally exact after their respective boundary simplifications. There is even a four-component implementation with the simplified boundary types that has the right final behavior. But no such implementation can preserve both parents' intermediate information. The failure is an elementary incompatible pair of transition requirements, not a missing numerical estimate or an unproved coherence assumption.

The claim is scoped to the fixed memoryless grid signature and its permitted boundary types. New hidden memory, extra communication, correlated choices not represented by the specified interfaces, or restoration of a finer boundary are changes of the realization problem, not counterexamples to it.

## 1 Concrete network

Use finite sets

  A={a0,a1}, K={0,1}, B={b0,b1,b2},
  C={c0,c1,c2}, L={0,1}, D={0,1}.

There are four components, with names and locations:

  upper left R:A->B,
  upper right T:B->C,
  lower left Q:K->L,
  lower right S:C x L->D.

The whole's external input is (a,k), and its output is d. Its wiring is R->T->S and Q->S. Define

  R={(a0,b0),(a1,b1),(a1,b2)},
  T={(b0,c2),(b1,c1),(b2,c0)},
  Q(k)=1-k,
  S(c,l)=s(c) XOR l,

where s(c0)=0 and s(c1)=s(c2)=1. Only R is nondeterministic. All other component transitions are deterministic. The lower-left component changes an external input and genuinely changes the final observable output; it is not a unit or unused component.

The whole behavior W is therefore

  W(a0,k)={1 XOR (1-k)},
  W(a1,k)={0,1}.

Two partitions of the component occurrences cross:

  rows:    {R,T} | {Q,S},
  columns: {R,Q} | {T,S}.

Their four intersections are exactly the four distinct component occurrences. This is not merely reassociation of three pieces along one ordered tree.

## 2 Individually exact parent decompositions

Let q_B:B->Y have Y={y0,y1}, with b0,b1 mapped to y0 and b2 mapped to y1. Let q_C:C->Z have Z={z0,z1}, with c0,c1 mapped to z0 and c2 mapped to z1.

In the row decomposition, abstract only the row boundary C through q_C. The top macro relation P:A->Z is

  P(a0)={z1},
  P(a1)={z0}.

The bottom macro V:Z x K->D is obtained from Q and S by existentially forgetting the concrete C-value. Thus

  V(z0,k)={0,1},
  V(z1,k)={1 XOR (1-k)}.

Their composite is exactly W.

In the column decomposition, abstract only the B coordinate of the column boundary B x L through q_B x id_L. The left macro M:A x K->Y x L has

  M(a0,k)={(y0,1-k)},
  M(a1,k)={(y0,1-k),(y1,1-k)}.

The right macro N:Y x L->D is formed from T and S by existential abstraction of B. Both b0 and b1 yield s=1, while b2 yields s=0, so

  N(y0,l)={1 XOR l},
  N(y1,l)={0 XOR l}.

Their composite is again exactly W. These identities hold for every external input, not only a selected trace.

## 3 The typed common-refinement problem

Keep the four-component grid and the prescribed simplified internal types Y,Z,L. Freeze the upper-left and lower-left component relations to the existing abstractions

  R_Y=q_B R,
  Q(k)=1-k.

A conservative grid refinement must supply an upper-right relation U:Y->Z such that contraction of the top row recovers the parent top macro literally:

  U R_Y = P.

It must also recover the other parent macros when their corresponding rows/columns are contracted. The first displayed equation is already a necessary condition, so failure of it proves failure of the full problem.

This convention preserves the parents' actual intermediate Z-observations, not only their final external behavior. No arbitrary additional wire from A or a hidden representative of B is available to U.

### Theorem Conservative crossing refinement is impossible

There is no relation U:Y->Z satisfying U R_Y=P. Consequently there is no conservative common refinement in this typed grid signature of the two exact parent decompositions above.

Proof. Since R_Y(a0)={y0} and P(a0)={z1}, any U satisfying the equation must have z1 in U(y0). But y0 also belongs to R_Y(a1), so z1 then belongs to (U R_Y)(a1). This contradicts P(a1)={z0}. QED.

The obstruction has the presentation

  a0 R_Y y0,
  a1 R_Y y0,
  a0 P z1,
  not(a1 P z1).

The shared allowed intermediate value y0 cannot carry the distinction required by the parent top-row transition. This uses transition-square compatibility, not only indistinguishability of one fixed output.

## 4 Extensional repair does not repair the conservative diagram

There is a grid with these same coarse boundary types and the correct final behavior. Choose

  U_*(y0)={z1},
  U_*(y1)={z0},

and let S_Z:Z x L->D be the existential abstraction of S, so S_Z(z0,l)={0,1} and S_Z(z1,l)={1 XOR l}.

Then the whole composite S_Z(U_* x id_L)(R_Y x Q) equals W: a0 reaches z1 only, and a1 can reach both z1 and z0 and therefore both outputs. But its top row maps a1 to {z0,z1}, not the required {z0}. Its right column at y1 likewise permits both outputs rather than the parent's singleton N(y1,l). It is therefore an extensional implementation, not a conservative refinement of the two parents.

This distinction prevents a weak success criterion from silently accepting a different internal decomposition. A search that checks only final behavior returns a realization here; a search for a common refinement of the existing typed implementations correctly returns an empty fibre.

## 5 Scope and role

The theorem does not say that the original concrete four-component network lacks a refinement. Restoring the actual B and C boundaries gives that network. Nor does it say no more expressive implementation can work. It identifies precisely the obstruction to preserving both parents inside the stated coarse boundary signature.

The construction embeds the serial interface-abstraction mismatch from Wiring_Exactness_and_Joint_Abstraction.md into genuine crossing row/column partitions; that embedding is explicit. The new item established here is the no-existence claim for a conservative coarse-typed grid, not merely failure of the canonical direct-image middle component.

All calculations are finite relation composition. This is a concrete negative test for the promised relative reconstruction theorem, not a claim to a novel general gluing principle. A general positive theorem must specify the allowable changes of boundary types and preserve these commuting transition squares, in addition to any state-observation or endpoint-exactness criteria.
