# Analytic monoid repair theorem for the active-path candidate

**Status and scope.** This is an elementary analytic theorem for a specified finite transformation-monoid witness family and its set-valued joint factorization probes. It does not identify noncommutative labels with original C5 commutative node scalars. The separate graph-active-slot and full-profile representation arguments must supply that application. No objective/CULF or multiplicity claim is made here.

## 1. The finite monoid and complete normal-form multiplication

Fix k≥4 and put t=k−1. On X={0,...,k−1}, let

    a=(k−1,1,1,2,...,k−2),  b=(1,2,1,...,1),

with multiplication fg=f∘g. Let M_k=⟨a,b⟩, including the identity. Define

    A_i=a^i                 (0≤i≤t),
    B_i=ba^i                (0≤i≤t),
    D_i=b²a^i               (0≤i≤t−2).

The two constants are A_t=const(1), B_t=const(2). Define the shorthand

    δ(s)=D_s if 0≤s≤t−2;
         A_(t−1) if s=t−1;
         A_t if s≥t.

The complete multiplication table is the following table of formulas, with column indices restricted to the displayed normal forms:

| left factor | right A_j | right B_j | right D_j |
|---|---|---|---|
| A_0 | A_j | B_j | D_j |
| A_i, i≥1 | A_min(i+j,t) | A_t | A_t |
| B_0 | B_j | δ(j) | B_j |
| B_i, i≥1 | B_min(i+j,t) | B_t | B_t |
| D_0 | δ(j) | B_j | D_j |
| D_i, i≥1 | δ(i+j) | A_t | A_t |

In particular b²a^(t−1)=A_(t−1), **not** A_t. This penultimate-row merge is important at k=4 as well as larger k.

**Proof and cardinality.** Direct transformation calculation gives ab=A_t, b³=b, and b²a^s=δ(s). These relations give the table, which is closed and contains both generators and the identity; every listed form is a word, hence the list is exhaustive. Distinctness can be read from the transformations:

- A_0 is the identity. For i≥1, A_i(0)=k−i and, for x≥1, A_i(x)=max(1,x−i).
- For 0≤i≤t−1, B_i(0)=1; B_t is constant 2. For x≥1, B_i(x)=2 exactly when x≤i+1, and is 1 otherwise. This also holds for i=0.
- D_i(0)=2. For x≥1, D_i(x)=1 exactly when x≤i+1, and is 2 otherwise.

The A_i with i≤t−2 have either ≥3 at 0 or are the identity. A_(t−1) has 2 at 0 and 1 everywhere else, so differs from every listed D_i. The B_i have value 2 at 1 whereas the A_i,D_i have value 1 there. Thresholds distinguish forms within each row; the two constants are distinct. Thus

    |M_k|=(t+1)+(t+1)+(t−1)=3k−2.

Associativity comes from actual function composition, not from an unverified presentation table.

## 2. Observation and the two repairs

Let H={A_0,B_0,D_0}={e,b,b²}. Let P0 be the partition {H,M_k\H}. The table shows H is a submonoid and its complement is a two-sided ideal. Thus membership in H is a homomorphism to the two-element monoid with multiplication AND, and P0 is a multiplication congruence.

For a partition P, write [x]_P for the class of x. Refinement means smaller equivalence relation/more observed information.

- S(P) is the coarsest refinement of P stable under left and right multiplication. Equivalently x~S(P)y iff every context u(−)v has equal P-observation on x,y. Elementary left/right multiplication by a,b suffices, since they generate M_k.
- The elementary cut step is

      c(P): x~y iff x~P y and F_P(x)=F_P(y),
      F_P(x)={([u]_P,[v]_P): uv=x}.

  C(P) is the stable result of iterating c. This is the coarsest P-refinement with representative-independent **joint ordered factorization-existence** outputs.

Every factorization output retains the ordered pair and its common source witness. Neither independent output marginals nor factorization counts are being substituted for this signature. Binary factorization, associativity and the identity give all finite ordered factorization-tree tests; finite cardinality is not itself the reason unbounded factorization syntax is covered.

## 3. Exact first cut repair

Define the index h(A_i)=h(B_i)=h(D_i)=i. Let Q be its k-block partition. Directly from the multiplication table,

    {(h(u),h(v)):uv=x} = {(j,l):j+l=i}              if h(x)=i<t;
    {(h(u),h(v)):uv=x} = {(0,t)} ∪ ({1,...,t}×{0,...,t})  if h(x)=t.

For the finite-index case necessity follows from the table; sufficiency uses A_jA_l, B_jA_l or D_jA_l according to the row of x. For the constant case positive left index followed by a B/D-leading right factor yields the required constant; the table supplies either constant at every index pair with positive left index. Index (0,t) is realized using identity. No other pair can occur.

Therefore Q is cut-stable. Conversely, any cut-stable refinement of P0 must distinguish all h indices: a nonconstant of index i has maximum i factors outside H in a factorization, while either constant admits arbitrarily many such factors (append a repeatedly). These are finite generated cut-tree predicates, invariant under cut stability by recursive joint lifting. Hence

    C(P0)=Q,  S(P0)=P0.

Q is not a multiplication congruence: A0~Q B0, but aA0=a has index 1 and aB0=ab=A_t has index t. Since k≥4, 1≠t. Thus C∘S and S∘C differ at P0 for every k in the family.

## 4. The least simultaneous S/C refinement is discrete

**Theorem.** Every partition E refining P0 and stable under both substitution and joint factorization is discrete. Therefore the least simultaneous S/C refinement exists and is the full identity partition on M_k.

**Proof, with explicit distinguishing predicates.** Such E refines Q by §3.

1. **Isolate the A row before its last two entries.** If 0≤i≤t−2, left multiplication by a sends A_i to A_(i+1), of index i+1<t, while it sends B_i and D_i (where present) to A_t, of index t. Thus A_i is separated from every other element of its Q fibre. In particular A_1 is an E-singleton; t≥3 is exactly what guarantees this.

2. **Separate the two constants by a joint cut.** A_t has a factorization with left factor A_1=a, namely a·b=A_t. B_t has no such factorization: the complete table gives

       aM_k ⊆ {A_1,...,A_t},

   which excludes B_t. Since the class of A_1 is a singleton, their joint factor signatures differ. Therefore A_t and B_t are E-distinct.

3. **Separate the penultimate A/B pair.** Right multiplication by b sends A_(t−1) to A_t and B_(t−1) to B_t, now distinguished.

4. **Separate every remaining B/D pair of positive index.** For 1≤i≤t−2, right multiplication by b sends B_i to B_t and D_i to A_t, now distinguished.

5. **Separate B_0 from D_0.** Right multiplication by the generated word ab sends B_0 to B_t and D_0 to A_t. Equivalently use right a followed by right b; D_0a=D_1 exists because k≥4.

Q already distinguishes different indices. At each nonterminal index the only possible members are A_i,B_i,D_i; steps 1,3–5 distinguish all of them, while step 2 distinguishes the terminal fibre. Hence E is discrete. ∎

This proof gives a uniform finite description of generated distinguishing tests: cut-depth predicates for the index, one left-a context, the existential cut predicate 'left factor is A_1', and right-b or right-ab contexts. It does not rely on exhaustively enumerating all observation partitions.

**Information necessity.** Starting from two observation blocks, every simultaneous quotient needs 3k−2 distinct states, hence at least ceil(log2(3k−2)) bits for an injective fixed-length representation. It retains at least 3k−4 additional blocks relative to the starting two-block partition. These are state/information lower bounds, not assertions about optimal running time.

**A finite repair schedule suffices.** The proof shows that C(P0), followed by S, followed by C, followed by S, is discrete. In the repeated saturated C∘S schedule this gives at most three nontrivial sweeps. Exact intermediate partition counts are not needed for the theorem. The family nevertheless requires more than the first S-then-C sweep, as proved in §3.

## 5. Exact elementary cut-stabilization complexity

Let P^(0)=P0 and P^(r+1)=c(P^(r)); c is one signature step, not the whole repair C.

- P^(1) has index blocks {0}, {1}, {2,...,t}.
- For r≥2, each index i<min(2^r,t) is isolated, index t is isolated, and the residual interval [2^r,t−1] is a single block when nonempty.

Thus |P^(r)|=min(k,2^r+2) for r≥2, and the exact number of nontrivial elementary cut steps is

    R(k)=max(2, ceil(log2(k−2))).

**Proof.** The joint-index formula gives the first step. At the second step, indices 2 and 3 distinguish by singleton-sum/mixed factor pairs, the residual/residual pair first appears at index 4, and the terminal index separates by the pair ({1},{0}), unavailable at any finite index ≥2. This proves the r=2 formula, also when some listed indices are absent.

For induction let d=2^r. Under the partition with singleton indices below d, a residual finite interval R and a singleton terminal index, finite indices below 2d have distinguishing singleton/singleton sum or singleton/R signatures. Index 2d−1 has no R/R factorization, while all finite indices ≥2d have one. All such indices ≥2d have the same saturated singleton/R, R/singleton and R/R signatures and no singleton/singleton signatures. The terminal class remains isolated. Hence the threshold doubles until the residual interval has at most one element, equivalent to 2^r≥k−2. ∎

This is a genuine uniform Ω(log k) stabilization necessity result for this elementary refinement scheme, separate from the constant upper bound on saturated-repair sweeps.

## 6. Boundary and interpretation conditions

The proof applies within one fixed unary full-profile sort carrying M_k as **operation witnesses**, not as object/interface grades. The legal multi-input extension uses active branch labels, with tuple substitution m_i n_ij, rather than an unordered noncommutative node product. To transport the theorem to the full graph class, the active-slot singleton lemma must guarantee that all admissible singleton cuts have exactly this paired-factorization meaning and that old graph/scalar metadata is fixed or observed unchanged. Additional observation predicates or cut constraints can invalidate the exact first-repair and round counts, although they may only strengthen a state lower bound once the required test embedding is proved.
