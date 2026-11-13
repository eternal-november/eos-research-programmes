# Partial-whole anchors can obstruct global cylinder reconstruction

## Abstract
A component can behave consistently on each of three overlapping ranges of system inputs, yet the three proposed identifications of its internal events need not fit together. Here every local decomposition is a correct decomposition of an actual restriction of one fixed finite-state whole. The restrictions really are Cartesian restrictions along input subsets. Nevertheless, walking around the three overlaps forces one internal event to become the other. Thus no single component realizes all the proposed local decompositions.

This is an explicit instance of ordinary permutation holonomy, not a claim of a new mechanism. It differs crucially from an invalid holonomy example using fully visible copies of the whole: each chart here sees only two of three input values. The four-component version below makes all four components dynamically active.

## 1 Minimal witnessed version

Let A={0,1,2}, B=C={*}. The fixed outer span R:A↝B has one event r_a at each input a. The fixed parent/whole span P:A↝C has actual events p_(a,u), u∈{0,1}, at each input a. Thus P is literally one fixed six-event whole.

Set A_1={0,1}, A_2={1,2}, A_3={2,0}. Restrict R and P along each inclusion A_i↪A by Cartesian pullback. Denote the restricted spans R_i,P_i. No actual witness is selectively dropped within an input fibre.

Each chart has T_i={0,1}, regarded as local events rather than globally identified events. Define actual bijections

    alpha_i(r_a,t)=p_(a,t XOR f_i(a)),

where f_1=f_2=0 and f_3(0)=0, f_3(2)=1. Set Q=S=id, N_i=T_i, beta_i=id, theta_i=alpha_i^{-1}. Every chart is an exact witnessed grid realization.

### Actual overlap comparisons

At a shared input a, the same event p_(a,u) determines the comparison

    g_ij(t)=t XOR f_i(a) XOR f_j(a).

This is forced by alpha_j(r_a,g_ij(t))=alpha_i(r_a,t). It is not independently supplied. The comparison is identity on overlap 1∩2={1}, swap on 2∩3={2}, and identity on 3∩1={0}. Each preserves the actual restricted whole pointwise. There is no triple overlap requiring another local condition.

### No simultaneous global realization

A global realization would consist of T, alpha:R;T≅P and chart identifications h_i:T_i≅T such that

    alpha(r_a,h_i(t))=alpha_i(r_a,t).

Since |P_a|=2, T has two events. Injectivity of alpha at each overlap forces h_j g_ij=h_i. Composing around the cycle gives h_1 swap=h_1, impossible for a bijection. Equivalently, chart 1 joins p_(0,0) to p_(1,0); chart 2 joins p_(1,0) to p_(2,0); chart 3 joins p_(2,0) to p_(0,1). The forced global middle partition identifies two different events in the same outer fibre.

The whole P certainly has other factorizations through R. The impossibility is of realizing ALL THE GIVEN LOCAL WITNESSED DECOMPOSITIONS, not of factoring its behavior at all.

### Matched positive

Replace f_3(2)=1 by f_3(2)=0. Then T=bits and alpha(r_a,t)=p_(a,t) realize all three charts. The fixed-data realization groupoid is contractible: a global middle event is forced by either event at input 0, and the charts determine its event at the other two inputs. All whole events, restrictions, endpoint types, and counts are unchanged; only the third chart's actual event pairing changes.

## 2 Four dynamically active components

This is not necessary for the holonomy proof, but makes the crossing-grid schema genuine rather than relying only on unit components.

Write x,k,b,c,l,d∈{0,1}. Use input interface A={0,1,2}×bits, and B=C=K=L=D=bits. Fixed outer components are:

- R: one event r_(a,x):(a,x)→b=1−x.
- Q: one event q_k:k→l=1−k.
- S: one event s_(c,l):(c,l)→d=c XOR l.

The fixed parent P has two events p_(a,x,u):(a,x)→c=x, u∈bits. Hence the fixed actual whole (P×Q);S has events

    (a,x,k,u),  input ((a,x),k), output x XOR (1−k).

For chart i restrict only the a input to A_i. Its hidden component T_i has events t_(b,v):b→c=1−b, v∈bits. Its second parent N_i has events n_(b,l,v):(b,l)→d=(1−b) XOR l. Define

    alpha_i(r_(a,x),t_(1−x,v)) = p_(a,x,v XOR f_i(a)),
    beta_i((t_(b,v),l),s_(1−b,l)) = n_(b,l,v).

The chart whole comparison is then forced:

    theta_i((p_(a,x,u),q_k),s_(x,1−k))
      = ((r_(a,x),q_k),n_(1−x,1−k,u XOR f_i(a))).

It is an endpoint-preserving actual bijection and satisfies the grid equation. Q is literally unchanged. Each local T_i is independent of both k and l, so each chart passes the cylinder Q/F/L tests. All visibility hypotheses hold.

On overlaps the forced T comparison is

    t_(b,v) -> t_(b,v XOR f_i(a) XOR f_j(a)),

with the corresponding comparison on N_i; these preserve the SAME actual whole events. At each b the previous identity/swap/identity cycle remains. Therefore no global T and alpha_0:R;T≅P can restrict to all three local charts, even allowing the only possible isomorphisms on their middle witnesses. Replacing f_3 by zero gives a global T and global N with precisely these formulas.

R changes the controlled state x; T changes b; Q changes k; S combines the two branches. The occurrence partitions {R,T}|{Q,S} and {R,Q}|{T,S} genuinely cross. The obstruction itself remains a witness-matching obstruction, not a mismatch of external transition behavior.

## 3 Exact scope: what is and is not fixed globally

P,R,Q,S and the whole (P×Q);S are globally fixed, literally. The restricted input charts are genuine Cartesian endpoint restrictions. The N_i and their witness identifications are local reconstruction data; their overlap identifications are FORCED by the actual whole and each theta_i. There is deliberately no already-given global N with coherent identifications to every N_i. Supplying such an N with a common theta would pre-solve precisely the descent issue being tested.

Thus the example applies to reconstructing a globally shared component from a network of locally correct witnessed crossing charts. It does not contradict the previous fixed-global-boundary theorem, nor the fact that fully visible charts anchored to the entire same whole have trivial forced holonomy. It also does not claim that this ordinary holonomy mechanism alone is the substantive new theorem sought.

## 4 Unbounded chart-family obstruction arity

The triangle extends to every n≥3. Let input indices be vertices 0,...,n−1 of a cycle. Chart i sees inputs {i,i+1 mod n}. Give every actual whole-input fibre two events. All charts pair equal bits except the final chart, which pairs opposite bits between inputs n−1 and 0. Use the same active-grid construction with a now ranging over these n indices.

A global event pairing is described, up to globally renaming its two middle events at each b, by bits g_a. The local chart equations say

    g_i XOR g_(i+1) = 0  (i<n−1),
    g_(n−1) XOR g_0 = 1.

Their XOR is 0=1, so the complete family has no reconstruction. Every proper subfamily removes an edge of the cycle and is a forest. Choose a g value at one vertex of each connected component and propagate along its edges; this satisfies all remaining equations. Therefore every proper subfamily does have a global realization, even when global alpha is required over all original inputs (assign any isolated inputs freely).

Consequently no fixed bound k on the number of charts jointly checked decides simultaneous reconstruction for all these finite input-cover networks: choose n>k. This is a precise higher-arity failure within the endpoint-Cartesian, same-whole, dynamically active grid family. It is still explained by standard cycle holonomy, not a distinct cohomological classification or new obstruction mechanism.
