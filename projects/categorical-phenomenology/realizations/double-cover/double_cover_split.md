# Split stochastic interfaces, double covers, and exact rank-two native widths

Research derivation and source audit, 3 November 2026.

## Main findings

1. For a two-sheeted cover P → X with associated real line bundle ℓ and k ≥ 1, a continuous equivariant stochastic split pair Q: P → Stoch(2,k), L: P → Stoch(k,2), QL = I₂, exists exactly when ℓ embeds in ε^(k−1). This is an existence statement, not a claim that a prescribed Q admits a continuous decoder.
2. More generally, the space of stochastic split pairs for r local states and k global slots is S_r-equivariantly homotopy equivalent to the deleted-product space D_r(Δ^(k−1)) = Hom(K_r,K_k). An explicit uniform threshold supplies the missing continuous decoder after modifying Q inside its original support cell.
3. For a fixed finite outcome alphabet and a time-homogeneous, deck-equivariant local two-state stochastic realization whose observable Hankel rank is two at every parameter, every globally labelled normalized signed realization already forces ℓ ↪ ε^(k−1). Therefore its exact continuous normalized signed and stochastic native widths coincide and equal g(ℓ)+1. No split maps are assumed for competing native realizations. No extra control is needed.
4. The topology is classical: Hom(K₂,K_k) is the antipodal (k−2)-sphere, and g(ℓ) is the unnormalized Schwarz genus of the cover under the usual paracompact hypotheses. The contribution here is the explicitly proved decoder repair and its typed use in native stochastic transfer and centered-Hankel extraction. No novelty certification is claimed.

## 1. Conventions and scope

Stoch(a,b) denotes entrywise nonnegative real a×b matrices whose rows sum to one. Write 1_j for the all-ones column of length j. A base is allowed to be disconnected or noncompact. A cover means a locally trivial principal Z₂-bundle, with deck involution τ, and ℓ = P ×_{Z₂} R for the sign representation. Set J = [[0,1],[1,0]]. A split pair satisfies

- Q(τp) = JQ(p),
- L(τp) = L(p)J,
- Q(p)L(p) = I₂.

A bundle embedding means a continuous fiberwise linear injection, whose image is a rank-one subbundle. No paracompactness is needed for the explicit equivalence below: ℓ already has the canonical metric |[p,t]| = |t|, and a given embedding can be normalized in the target Euclidean norm. Paracompactness enters only the open-cover characterization by Schwarz genus and optional smoothing of a merely continuous embedding.

For X nonempty, k=1 is impossible on both sides: QL cannot have rank two and ℓ cannot embed in rank zero. We use only positive integer state counts. For X empty all maps and conditions are vacuous, including the fiberwise injection over the empty base; minimum-width conventions for an empty experiment are best left separately declared. All width statements below assume X nonempty.

## 2. Exact double-cover split theorem

**Theorem 1.** For k≥1 the following are equivalent:

(a) A continuous equivariant stochastic split pair (Q,L) exists.

(b) There is a continuous odd nonzero map P → 1_k^⊥.

(c) ℓ embeds in ε^(k−1).

For k≥2 these are also equivalent to an equivariant map P → S^(k−2), with the antipodal target action.

**Necessity.** Let q₊ and q₋ be the rows of Q and put d=q₊−q₋. Row normalization gives d1_k=0; equivariance gives d(τp)=−d(p). Since dL=(1,−1), d never vanishes. The map [p,t] ↦ (x,t d(p)) is the required bundle embedding. This argument does not require a choice of metric on the base.

**Sufficiency, with a uniform buffer.** Normalize the odd map so that u(p)∈1_k^⊥ and ||u(p)||₂=1. Put

c_k=1/√(k(k−1)), and choose a constant 0<η<c_k.

Every such u has max_i u_i≥c_k and min_i u_i≤−c_k. To prove the first inequality, let M=max_i u_i>0, S=Σ_{u_i>0}u_i and note S≤(k−1)M. Then

1 = Σ_{u_i>0}u_i² + Σ_{u_i<0}u_i² ≤ MS + S² ≤ k(k−1)M².

Apply this to −u for the other inequality. The bound is sharp, as shown by one coordinate −(k−1)c_k and the remaining k−1 coordinates c_k.

Define

q₊,i(u) = (u_i−η)_+ / Σ_j (u_j−η)_+,
q₋,i(u) = q₊,i(−u),
L_{i,+}(u) = [1+clip(u_i/η)]/2,
L_{i,−}(u) = [1−clip(u_i/η)]/2,

where clip(t)=max(−1,min(1,t)). Both denominators are positive. If q₊,i>0 then u_i>η and L_i=(1,0); if q₋,i>0 then u_i<−η and L_i=(0,1). Thus QL=I₂. The rows are stochastic, and replacing u by −u swaps the two Q rows and the two L columns. The buffer around zero is exactly what makes the decoder continuous.

### Smooth version

If X and P are smooth manifolds and u is smooth, choose a smooth function φ:R→[0,∞) with φ(t)=0 for t≤η and φ(t)>0 for t>η, and a smooth odd h:R→[−1,1] with h(t)=±1 for ±t≥η. Replace positive parts by φ and clip by h. All identities remain exact, and Q,L are smooth. On the usual paracompact smooth manifolds, a continuous odd nonzero map can be approximated smoothly, antisymmetrized, and normalized, so a continuous embedding also yields a smooth split pair. On an arbitrary smooth space without an approximation theorem, assume a smooth embedding explicitly.

This does not establish a real-analytic construction. In fact, on a connected real-analytic P with nontrivial deck action, a real-analytic equivariant stochastic Q with disjoint row supports cannot exist: q₊,i q₋,i=0 and analytic continuation force one factor to vanish identically; equivariance then forces both to vanish identically, for every i. This observation concerns split interfaces, not all possible analytic native realizations.

## 3. General r-state decoder repair and homotopy equivalence

Let

D_{r,k} = {Q∈Stoch(r,k): distinct rows have disjoint supports},
S_{r,k} = {(Q,L)∈Stoch(r,k)×Stoch(k,r): QL=I_r}.

Assume 1≤r≤k. The group S_r acts by Q↦AQ and L↦LA^(−1), where A is a permutation matrix.

**Lemma.** Every split pair projects to D_{r,k}. Indeed, for a≠b, 0=(QL)_{ab}=Σ_iQ_{ai}L_{ib}; consequently Q_{ai}>0 forces L_i=e_a. A column cannot be occupied by two different Q rows.

**Theorem 2.** The projection pr:S_{r,k}→D_{r,k}, (Q,L)↦Q, is an S_r-equivariant homotopy equivalence. In particular, for any base B and any principal S_r-bundle E→B, an equivariant map E→D_{r,k} exists if and only if an equivariant split pair exists.

**Explicit construction.** Fix 0<η<1/k and choose θ:[0,1]→[0,1] continuous with θ(0)=0 and θ(t)=1 for t≥η. For example θ(t)=min(t/η,1). Define

F(Q)_{ai} = (Q_{ai}−η)_+ / Σ_j (Q_{aj}−η)_+,
B(Q)_{ia} = θ(Q_{ai}) + [1−Σ_b θ(Q_{bi})]/r.

Every row of Q has an entry at least 1/k, so every denominator is positive. At most one Q_{ai} in any fixed column i is nonzero. Therefore Σ_bθ(Q_{bi})≤1, B is entrywise nonnegative, and Σ_aB_{ia}=1. If F(Q)_{ai}>0, then Q_{ai}>η, θ(Q_{ai})=1 and every other θ in that column vanishes. Hence B_i=e_a and F(Q)B(Q)=I_r. The map s(Q)=(F(Q),B(Q)) is continuous and S_r-equivariant.

The straight path H_t(Q)=(1−t)Q+tF(Q) remains row stochastic and has support contained in that of Q. For t<1 its support is exactly that of Q, so this is a support-shrinking, cell-preserving homotopy, with no newly occupied slots. This proves pr∘s≃id_D equivariantly.

For an existing split pair (Q,L), the same support argument gives H_t(Q)L=I_r. Thus (Q,L) is homotopic within S_{r,k} to (F(Q),L). Holding F(Q) fixed, convexly interpolate the decoder from L to B(Q); both endpoints decode F(Q) exactly, so every intermediate decoder does also. The concatenation gives id_S≃s∘pr equivariantly. No lifting property of pr and no local continuous choice of arbitrary decoder are assumed.

The theorem also works for any subgroup of S_r. For r>k and nonempty base both spaces are empty. For r=1 the construction and conclusion remain valid.

### Why the original Q may have no decoder

On t∈[−1/2,1/2], with three slots, set

q₊(t)=(−t)_+e₁+[1−(−t)_+]e₂,
q₋(t)=t_+e₁+(1−t_+)e₃.

These are continuous disjoint-support probability rows. Any stochastic L with QL=I₂ must have L₁=e₊ for t<0 and L₁=e₋ for t>0. Therefore no continuous L exists for this prescribed Q. The obstruction disappears after thresholding because slot 1 remains vacant throughout a nonzero interval around t=0.

### Smooth repair

For smooth Q, replace (t−η)_+ by a smooth nonnegative cutoff φ(t), zero for t≤η and positive for t>η. Choose smooth θ with θ(0)=0, 0≤θ≤1, and θ(t)=1 for t≥η. The formulas remain valid and become smooth. The same straight homotopy stays split, and its two stages can be reparameterized by flat smooth step functions. This is not a claim that arbitrary continuous Hom-valued maps can be smoothed inside the singular Hom complex without modification; it is a construction for smooth Q and a continuous existence theorem in general.

## 4. Transfer of fixed-outcome stochastic instruments

Let E→B be a principal S_r-bundle. Suppose a finite public outcome set Y is fixed, with continuous local matrices M_y:E→R_{≥0}^{r×r} and a probability preparation π:E→Stoch(1,r), satisfying

M_y(A·e)=A M_y(e) A^(−1),
π(A·e)=π(e)A^(−1),
(Σ_y M_y)1_r=1_r.

We use a left action on E; the corresponding identities are Q′=AQ, L′=LA^(−1), M′_y=AM_yA^(−1), π′=πA^(−1). Define

ρ=πQ,
N_y=LM_yQ.

These are invariant under change of local labeling and descend to B. They are nonnegative, ρ1_k=1, and

(Σ_yN_y)1_k=L(Σ_yM_y)Q1_k=L1_r=1_k.

Since QL=I_r and Q1_k=1_r, for every word w=y₁…y_n,

ρN_{y₁}…N_{y_n}1_k = πM_{y₁}…M_{y_n}1_r.

Moreover N_yL=LM_y and ρL=π. This is an exact statewise stochastic comparison, not just equality of one initial output law. It works simultaneously for any finite collection of public actions a with outcome kernels M_{a,y} and Σ_yM_{a,y}1_r=1_r. Word-by-word equality gives equality for adaptive policies as well. The external parameter stays fixed during each word. There is no cross-parameter identity Q_xL_{x′}=I_r and no parameter-transport operation is supplied.

For r≥3, Theorem 2 classifies existence of these split-interface lifts. It is not by itself a lower bound on all arbitrary positive native realizations of the same observed law. Section 5 supplies a separate native lower bound specifically in observable rank two.

## 5. All-native lower bound in the two-state case

Return to the double cover P→X. Let π:P→Stoch(1,2) and M_y:P→R_{≥0}^{2×2} satisfy π(τp)=π(p)J, M_y(τp)=JM_y(p)J, and (Σ_yM_y)1₂=1₂. Assume Y is finite and words use the same matrices at each stage. Define f_x(w)=π(p)M_w(p)1₂. These scalar functions descend to X.

For each outcome define real scalars

α_y(p) = first coordinate of [π(p)M_y(p)−f_x(y)π(p)],
β_z(p) = (M_z(p)1₂)_+ − (M_z(p)1₂)_−.

Here subscripts + and − name the two coordinates; α is not a positive-part operation. The centered prefix row is α_y(1,−1), so

C_{yz}(x):=f_x(yz)−f_x(y)f_x(z)=α_y(p)β_z(p).

Both α and β change sign under τ. The matrix C is the centered two-letter Hankel matrix, or multiplicativity defect. It is the probabilistic covariance of consecutive output indicators only when the first- and second-position marginals agree, for example when π is stationary. No stationarity is assumed here.

**Lemma.** In this normalized two-dimensional time-homogeneous setting, the full observable Hankel rank is two if and only if C is nonzero.

If C=0, its outer-product factorization forces α=0 or β=0. If α=0, πM_y=f(y)π for every y; induction gives f(w)=∏_j f(y_j). If β=0, M_z1₂=c_z1₂ for every z; induction gives the same rank-one conclusion, with f(z)=c_z. Conversely C≠0 is a nonzero Schur complement of the empty-word entry in a one-letter Hankel block, hence its rank is at least two, and the given local realization bounds it by two. This argument is specific to dimension two; delayed observability in general larger systems requires longer windows.

Now let any continuous native k-coordinate real realization on X have preparation ρ, matrices N_y and fixed terminal 1_k, with ρ1_k=1. It may be nonminimal, have unreachable states, have signed entries, and need not be related to the local model by any comparison maps. Assume it matches f(y) and f(yz). Set

d(p)=Σ_y α_y(p)[ρ(x)N_y(x)−f_x(y)ρ(x)].

Then d is continuous and odd, and d1_k=0 by the one-letter identities. By the two-letter identities,

d(p)N_z(x)1_k=Σ_yα_y(p)C_{yz}(x)=||α(p)||²β_z(p).

If the local observable rank is two everywhere, α and β are both nonzero everywhere; consequently d never vanishes. Thus ℓ embeds in 1_k^⊥≅ε^(k−1).

**Theorem 3 (exact native width).** Under the preceding rank-two hypotheses, let g(ℓ) be the least n≥1 such that ℓ embeds in ε^n. Then

minimum continuous stochastic native width
= minimum continuous normalized signed native width
= g(ℓ)+1.

The lower bound is the d construction and applies even to competitors that match only words of length at most two. The upper bound is Theorem 1 plus Section 4, which gives a nonnegative stochastic all-word realization. Thus every globally finite normalized native realization must pay the same topological cost in the two-state case. This does not claim the same answer when the terminal covector may vary.

The finite outcome alphabet automatically gives g(ℓ)≤|Y|−1: β is a nonzero odd vector and Σ_zβ_z=0. Hence the width is finite and at most |Y|. In particular, one fixed binary-output instrument cannot support a nontrivial two-state cover while remaining observable rank two everywhere. A single instrument with sufficiently many outcomes suffices; one globally nonvanishing scalar discriminator would trivialize ℓ.

With finite public actions, use labels (a,y), with all finite action sequences permitted. The same outer-product and induction proof works. For each a, Σ_yβ_{a,y}=0, giving g(ℓ)≤Σ_a(|Y_a|−1). No extra action is required for a rank-two uncontrolled law. If the cover is invisible, or rank drops, there is no universal lower bound: choosing all M_y=c_yI₂ gives a globally one-state IID law on any cover.

### Observable recovery of the line bundle

The nonzero rank-one column-image bundle im(C) is canonically isomorphic to ℓ: send [p,t] to tα(p). Similarly the row-image line is represented by β. Thus the line cover used by the lower bound is reconstructible from the one- and two-letter tables. Supplying an arbitrary finite table with rank-one centered part does not by itself supply an all-word two-state model; the upper realization theorem retains its model promise.

### Explicit two-step uniform robustness

Assume X is compact, set m=|Y| and c=min_x||C_x||_F>0. If a continuous normalized stochastic k-state competitor approximates every one- and two-letter probability with uniform absolute error ε<c/(3m), then ℓ still embeds in ε^(k−1).

Indeed let a(p)=α(p)/||α(p)||, let f′(w)=ρN_w1_k, C′_{yz}=f′(yz)−f′(y)f′(z), and form

d(p)=Σ_y a_y(p)[ρN_y−f′(y)ρ].

This is exactly centered, even when the competitor does not match the target, and dN_z1_k=(aᵀC′)_z. Since all stochastic one-letter probabilities lie in [0,1], each entry of C′−C has absolute value at most 3ε. Thus ||aᵀ(C′−C)||₂≤3mε, whereas ||aᵀC||₂=||C||_F≥c. Hence d is odd and nonzero. For signed normalized competitors, matching one-letter probabilities within ε bounds them by 1+ε in absolute value; the same argument works under m(3ε+ε²)<c. No bounds on competitor matrices, no minimality, and no assumptions on their reachable subspaces are needed. This is a uniform-in-parameter finite-horizon statement, not a certificate from finitely many parameter samples without regularity/coverage assumptions.

## 6. Held mixture specialization and explicit projective examples

Let v₊(p),v₋(p) be distinct probability vectors in Δ(Y), swapping under τ. Let positive weights w₊,w₋ sum to one and swap under τ. Put M_y=diag(v₊,y,v₋,y) and π=(w₊,w₋). Define a=v₊−v₋ and μ=w₊v₊+w₋v₋. Then

C_{yz}=w₊w₋ a_y a_z.

A particularly simple native extractor is

d(p)=Σ_y a_y(p)[ρN_y−μ_yρ],

d1_k=0,
dN_z1_k=w₊w₋||a||²a_z.

Thus Theorem 3 applies with arbitrary positive continuously varying weights and parameter-dependent distinct atoms. A zero weight or collision invalidates this proof exactly where the observable rank drops. Uniform mixtures have w₊w₋=1/4.

For X=RP^d and P=S^d with the antipodal cover, choose an isometry A:R^(d+1)→1_(d+2)^⊥, put c=1_(d+2)^T/(d+2), and define

v₊(u)=c+δ Au,
v₋(u)=c−δ Au,

with 0<δ<1/(d+2). These are distinct strictly positive probability vectors. Use the uniform held mixture. The associated ℓ is the tautological line bundle; g(ℓ)=d+1. Therefore the exact continuous stochastic and normalized signed widths are both d+2, despite every pointwise law having width two. The lower bound follows from Borsuk–Ulam or w₁(ℓ)^d≠0; the upper bound follows from the explicit inclusion into R^(d+1). For d=1 this recovers width three over the nontrivial circle double cover. This is a normalization/topology cost, not a positive-versus-signed gap.

## 7. Classical topology and source audit

### Classical stochastic recovery

The pointwise disjoint-support characterization is also classical: Ay, Jost, Lê and Schwachhöfer, *Information geometry and sufficient statistics*, Proposition 4.7, describe Markov congruent embeddings through Markov left inverses and trace this to Chentsov Lemmas 6.1 and 9.5. This is the pointwise recovery structure, not a claim that prescribed continuous encoders have continuous decoders. [Primary paper](https://arxiv.org/pdf/1207.6736).

### Hom complexes and deleted products

The points of D_{r,k} are precisely r probability vectors with pairwise disjoint supports, the standard polyhedral realization of Hom(K_r,K_k). This identification and the topology of these spaces are established prior art. Babson–Kozlov, Proposition 4.3, identify Hom(K₂,K_k) with the boundary of a centrally symmetric polytope, with row swapping corresponding to central symmetry; Remark 4.4 explicitly connects the complete-graph Hom space with deleted products. Proposition 4.5 gives the wedge-of-(k−r)-spheres homotopy type for general r. [Primary paper](https://arxiv.org/pdf/math/0310056).

For r=2 there is also the direct formula Q↦q₊−q₋. Its image is {z∈1_k^⊥:||z||₁=2}, and its inverse takes the positive and negative coordinate parts. This is an equivariant homeomorphism onto a polyhedral sphere; radial projection gives the ordinary antipodal S^(k−2). Dover–Özaydın state this L¹-sphere description explicitly in the introduction, page 3. [Primary paper](https://arxiv.org/pdf/1302.2831).

Abrams–Gay–Hower identify D_r(Δ^n) as the discretized configuration space, discuss the deleted-product terminology for two points, and prove the wedge-of-(n−r+1)-spheres theorem. [Primary paper, Theorem 1.1 and Section 2](https://arxiv.org/pdf/1009.2935). This is not the same as taking an arbitrary ordinary configuration of distinct points without the disjoint-support constraint.

Theorem 2 adds an explicit decoder-preserving homotopy argument. The inspected Hom/deleted-product results do not themselves assert the needed continuous stochastic decoder. The direct argument above establishes it without making that attribution.

### Schwarz genus and Borsuk–Ulam

For a paracompact Hausdorff base, g(ℓ) equals the unnormalized Schwarz genus of P→X: the minimum number n of open subsets covering X on each of which the cover has a section. An odd nonzero map P→R^n gives such an open cover using its nonzero coordinates, with the positive sign selecting a sheet. Conversely, local sections and a subordinate partition of unity give n odd coordinate functions with no common zero. Normalizing gives P→S^(n−1). This proves the equivalence directly and fixes the convention: a trivial nonempty cover has genus one, so split/native width is genus plus one.

The classical fiberwise-join characterization is Schwarz’s theorem; Pavešić restates it as Theorem 2.5, identifying genus ≤n with a section of the n-fold fiberwise join. For a double cover that join is the sphere bundle of nℓ. [Pavešić primary paper](https://arxiv.org/pdf/1901.00652); [Schwarz original publication record](https://www.mathnet.ru/eng/mmo132).

On CW bases, an embedding ℓ↪ε^n is equivalently a classifying map that factors, up to homotopy, through RP^(n−1). Thus w₁(ℓ)^n=0 is necessary. Its converse is not asserted in general: higher obstruction information may remain. On RP^d the standard cohomology or Borsuk–Ulam calculation makes g(ℓ)=d+1 sharp.

### Relationship to the supplied circle report

The supplied report correctly warns that a prescribed disjoint-support Q may lack a continuous decoder; the interval example above confirms this. It can now add that there is no further existence-level obstruction: thresholding Q produces a decoder, and the split-pair space has the same equivariant homotopy type as its Hom space.

The report’s p=2 nontrivial-monodromy circle case agrees with Theorem 3: both normalized signed and stochastic widths equal three. Its three-component even-monodromy example still displays a genuinely positive-versus-signed gap. Nothing here extends the rank-two centered-Hankel lower bound to arbitrary higher-rank positive native realizations. The same paper’s fixed-parameter and normalization cautions remain essential.

## 8. Evidence boundary

The proofs above establish the claims under their written assumptions; numerical checks are optional regression checks, not evidence for the topology. The source search verified close classical antecedents, not priority. In particular, neither the broad local/global obstruction, the antipodal sphere identification, the genus invariant, nor the usual stochastic intertwiner should be described as new. Whether the explicit buffered decoder homotopy and the exact rank-two native-width formulation already appear elsewhere remains an open bibliographic question.

### Regression check

The accompanying `check_double_cover_split.py` checks general r,k repair and homotopies, permutation equivariance, the sphere buffer, signed normalized coordinate changes, centered-Hankel extraction, and three-step word transfer. All checks passed; maximum residual was 8.88×10^(−16). It is a formula regression, not a proof of the topological or bibliographic claims.
