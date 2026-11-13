# Four component witnessed crossing examples

## Plain language summary

This example separates two questions that an ordinary square-completion theorem can conflate. Can the parent decompositions be explained by some intermediate component that is allowed to see an extra control signal? And can they be explained by the actual four-component grid, where the upper-right component is not allowed to see that signal?

Every support and counting test succeeds in the negative example. There is even a coherent witnessed square completion. But its explanation of which upper-right event occurred depends on the lower-left control signal. Removing that unauthorized dependence is impossible while retaining the supplied identification of whole-system events. Thus no genuine four-component common refinement exists. A matched positive example changes only that event identification and does admit the required grid.

All four components perform nonidentity operations. The extra event witnesses are retained transition occurrences, not disposable labels: the supplied whole-system matching identifies them in a specified way. If those occurrences are deliberately forgotten, the obstruction disappears, which is exactly the distinction being tested.

## 1 Interfaces and fixed components

Every interface A,B,C,K,L,D is the two-element set F_2={0,1}. Write XOR for addition modulo two and NOT x=1-x.

The four physical positions are

  upper left R:A->B,
  upper right T:B->C, to be reconstructed,
  lower left Q:K->L,
  lower right S:C x L->D.

The external input is (a,k), and the output is d. The upper chain is R then T then S; the lower-left component Q supplies the second input to S.

The fixed spans are:

- R has actual witness r_(a,e) for a,e in F_2, with endpoints a and b=NOT a. Thus every state transition has two retained events e.
- Q has witness q_k with endpoints k and l=NOT k. It is the NOT function graph, with one witness per input.
- S has witness s_(c,l) with input (c,l) and output d=c XOR l. It is the XOR function graph.

The two prescribed macro spans are:

- P:A->C has witness p_(a,e,v), for a,e,v in F_2, with endpoints a and c=a. There are four retained macro events for each a.
- N:B x L->D has witness n_(b,l,u), for b,l,u in F_2, with endpoints (b,l) and d=(NOT b) XOR l. There are two events for each (b,l).

The parent decompositions are rows and columns:

  rows:    {R,T} | {Q,S},
  columns: {R,Q} | {T,S}.

All four intersections are distinct nonempty component occurrences. Q is not an identity or an unused padding component: it negates an actual external control bit, and S uses that bit to change the final output. R and the candidate T each negate their own state bit; S depends on both of its inputs.

The row assembly has witnesses (p_(a,e,v),q_k,s_(a,l)), with l=NOT k. The column assembly has witnesses (r_(a,e),q_k,n_(NOT a,l,u)). Both have external endpoints

  (a,k) -> d=a XOR (NOT k)

and four whole events per external input.

## 2 The prescribed twisted matching

Define the boundary-preserving bijection theta between the row and column whole-witness sets by

  theta(p_(a,e,v),q_k,s_(a,l))
    = (r_(a,e),q_k,n_(NOT a,l, v XOR (e*l))),

where l=NOT k and e*l is ordinary bit multiplication. Its inverse uses the same formula v=u XOR(e*l), so it is a genuine bijection. It preserves the actual q witness, not only its endpoint.

The whole can be taken literally to be the row assembly, with theta identifying the column assembly with it. Thus the input includes one fixed whole with two witnessed decompositions, not merely two relations having the same support.

## 3 Every ordinary square test succeeds

Regard the data only as a square with left span R x Q, right span S, top span P x Q, and bottom span N. There is a coherent intermediate span

  U_square : B x L -> C x L

whose witness t_(b,l,u) has endpoints (b,l) and (NOT b,l), with u in F_2.

Define its left factorization bijection by

  alpha_square((r_(a,e),q_k),t_(NOT a,l,u))
    = (p_(a,e,u XOR(e*l)),q_k),

and its right factorization bijection by

  beta_square(t_(b,l,u),s_(NOT b,l))=n_(b,l,u).

Each is bijective on every full interface profile. Substituting them into theta gives the literal square-coherence equation. Therefore the ordinary witnessed square completion exists. In particular its rectangle/holonomy criterion succeeds, not just its Boolean support or its cardinality equations.

The remaining issue is that U_square is allowed to depend on l. A genuine upper-right component T:B->C is not. The required middle must be T x id_L, and the left factorization must be alpha_0 x id_Q for one alpha_0:R;T->P independent of Q.

## 4 No genuine four-component realization

A genuine grid realization consists of a finite span T:B->C, bijections

  alpha_0:R x_B T -> P,
  beta:(T x id_L) x_(C x L) S -> N,

and the fixed coherence equation

  theta(alpha_0(r,t),q,s)=(r,q,beta(t,l,s)).

Here q ends at l, and s begins at (right(t),l). The only allowed inputs to T are its B endpoints and its own event; it cannot inspect l or q.

### Theorem The twisted grid has no realization

No such T, alpha_0 and beta exist.

Proof. The fibre-cardinality equations from alpha_0 imply that T has exactly two witnesses over (b,NOT b) and no witnesses over (b,c) with c different from NOT b. Fix a and any one witness t over (NOT a,a).

Since theta returns the same R-event e that appears in its P-event, the coherence equation forces

  alpha_0(r_(a,e),t)=p_(a,e,v_e(t))

for some bit v_e(t). Define b_l(t) by

  beta(t,l,s_(a,l))=n_(NOT a,l,b_l(t)).

The coherence equation becomes

  b_l(t)=v_e(t) XOR(e*l)

for every e,l in F_2.

Taking e=0 gives b_0(t)=b_1(t)=v_0(t). Taking e=1,l=0 gives v_1(t)=v_0(t). Taking e=1,l=1 then gives v_1(t) XOR1=v_0(t), a contradiction. QED.

The proof allows arbitrary event sets and arbitrary bijections for T. It does not assume that T uses the same event names as the displayed square completion. Relabelling the two T events cannot remove the contradiction.

### Cylinder interpretation

For a fixed l and square-middle event u, alpha_square determines an actual R-labelled tile of the four P-events:

  e -> (e, u XOR(e*l)).

At l=0, the two tiles are

  {(0,0),(1,0)} and {(0,1),(1,1)}.

At l=1, they are

  {(0,0),(1,1)} and {(0,1),(1,0)}.

These are different partitions of the same retained P-event set, with their R labels fixed. No permutation of the two tile names makes them agree. This is the failure of the cylinder condition: a common T would require one and the same R-labelled decomposition of P at both l values.

This obstruction occurs after an ordinary square filler has been constructed. It is therefore not merely the old one-interval interpolation obstruction in different notation.

## 5 Positive comparison with all four components active

Keep every interface, fixed component, macro span, event count and external behavior unchanged. Replace theta by the untwisted matching

  theta_plus(p_(a,e,v),q_k,s_(a,l))
    = (r_(a,e),q_k,n_(NOT a,l,v)).

Let T have witnesses t_(b,u), with endpoints b and c=NOT b. Set

  alpha_0(r_(a,e),t_(NOT a,u))=p_(a,e,u),
  beta(t_(b,u),l,s_(NOT b,l))=n_(b,l,u).

These are bijections and satisfy the coherence equation for theta_plus. This gives an actual four-component common refinement. Its support, counts and individual component behaviors are identical to those of the negative example. Only the specified whole-event matching differs.

The positive and negative cases therefore test whether a reconstruction theorem retains the particular relationship between the two parent decompositions, not just their supports or event cardinalities.

## 6 A separate obstruction from actual parallel witnesses

The preceding negative example fails agreement across the two L values. A second fixture isolates the stronger requirement that an individual middle witness have the same meaning for every actual Q witness, even when their L values agree.

Keep the bit interfaces, R,S,P,N and their behaviors unchanged. Replace Q by a NOT span having two actual witnesses q_(k,j) per input k, with j in F_2 and output l=NOT k. Define

  theta_Q(p_(a,e,v),q_(k,j),s_(a,l))
    = (r_(a,e),q_(k,j),n_(NOT a,l,v XOR j)).

This preserves the actual q witness and all endpoints. Its source and target have eight whole witnesses per (a,k). An ordinary square filler again has two events u at each (b,l), with

  alpha_square((r_(a,e),q_(k,j)),u)
    = (p_(a,e,u XOR j),q_(k,j)),
  beta_square(u,s_(a,l))=n_(NOT a,l,u).

Thus every ordinary square condition and actual Q-witness preservation succeeds.

For each fixed j, the unordered set of R-labelled P-tiles is the same:

  { {(0,0),(1,0)}, {(0,1),(1,1)} }.

Changing j merely exchanges the names of the two tiles. Nevertheless, for one fixed canonical square-middle event u, its actual descriptor is e->(e,u XOR j), which changes with j. This is precisely Test F failure. Comparing only descriptor sets would miss it.

No genuine T is possible. For any fixed t and e, alpha_0 chooses one P-event bit v_e(t), independently of q. Coherence would require the same beta_l(t) to have event bit v_e(t) for j=0 and v_e(t) XOR1 for j=1. The two requirements contradict one another. A q-dependent relabelling of the intermediate events repairs the ordinary square but is forbidden for a single T with a fixed beta. This is why the cylinder theorem tests actual descriptors, not only the existence of isomorphic tile sets.

## 7 What changing the specification would do

Allowing T to see l admits U_square and repairs the first, L-dependent negative example, but changes the permitted interface of the upper-right component. It does not repair the separate Test F example: there the missing information is the actual Q-event j, not its L endpoint, so access to j or a change of the prescribed witness matching would be required. Forgetting the event witnesses removes both obstructions at the relational level. Replacing theta by theta_plus changes the prescribed identification of the whole's decompositions. None of these changes is a realization of its original fixed typed witnessed problem.

No claim is made that this is a deployed robotics example. It is a fully specified, finite, nondegenerate test of the four-corner reconstruction theorem. The actual positive criterion is given in the companion crossing-grid cylinder theorem.
