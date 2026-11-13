# Countable progress under wiring: constructive bridge and unresolved lift

Independent challenge/derivation, 2026-10-31. This note separates standard termination/small-gain arguments from the reconstruction bridge. It does not claim a general operational lift of free Isbell comparisons.

## Main findings

1. Local termination certificates do not compose without a routing-sensitive progress condition. A finite matrix of locally checked return-potential gains gives such a condition and handles countably infinite component state spaces.
2. A canonical-looking span can transport progress without any stochastic section: pull a potential back along its left leg, then take a fibrewise infimum along a surjective, exact operational right leg.
3. This bridge requires actual transition kernels and step-sensitive intertwining maps on the canonical apex and middle. Abstract CFS classes and external preparation/test equality do not provide them.
4. Fibre-infimum transport composes exactly on full set-theoretic pullbacks. A formal mixed pullback need not lift to such an operational pullback; equality of transition marginals does not identify their joint coupling. This is a real remaining coherence obligation, not solved by formal uniqueness.

Conventions: kernels act backward on nonnegative functions: Qv(x)=sum_y Q(y|x)v(y). Q is the substochastic internal continuation kernel. Disappearance from Q counts stopping; calling it successful exit additionally requires that all lost continuation mass is accounted for by an admitted output, rather than killing or failure.

## 1. Elementary obstruction

Module A receives a token, takes one step and sends it to B. Module B receives a token, takes one step and sends it to A. Each invocation terminates deterministically in one step; connecting their return ports gives an infinite alternating execution with probability one.

Thus local first-exit normalization is not enough. Nor is the existence of a finite path to an exit from every countable state: the biased walk already established in the companion gives exit probability 1/2 versus 1 on the same support. Neither an infinite graph path nor its mere absence is the relevant quantitative invariant.

## 2. Explicit local-to-global mechanism

There are finitely many modules i, with countable entry states X_i. The entry state must retain all persistent/shared hidden state relevant to the next invocation. A completed invocation either exits the network or returns to entry state y of module j. Its actual joint return kernel is L_ij(y|x). Separately certify that every invocation itself exits internally almost surely and has finite conditional expected duration g_i(x).

Choose finite functions u_i:X_i->[1,infinity). Prove local port-sensitive inequalities

    L_ij u_j(x) <= a_ij u_i(x),   a_ij >= 0.

These are quantitative postconditions of an invocation, INCLUDING its actual wiring/routing, not independent marginal output assertions. The nonnegative finite gain matrix A=(a_ij) is then checked algebraically. If positive w and lambda<1 satisfy

    A w <= lambda w,

rescale w so min_i w_i>=1 and define W(i,x)=w_i u_i(x). The actual macro-continuation kernel L obeys

    L W(i,x) = sum_j w_j L_ij u_j(x)
             <= (Aw)_i u_i(x)
             <= lambda W(i,x).

Since W>=1, survival after n completed invocations is at most lambda^n W(i,x). The expected number of invocations is at most W(i,x)/(1-lambda). This DERIVES global almost-sure stopping; it does not assume it.

If g_i(x)<=d_i u_i(x), put C=max_i(d_i/w_i). The expected total number of microscopic steps is at most C W(i,x)/(1-lambda), by conditioning invocation-by-invocation and Tonelli. A module with almost-sure but infinite-mean duration still permits the almost-sure macro argument, but not this expected-runtime bound. External entrance prefixes need their own duration and initial-potential bound.

For finite A, spectral radius rho(A)<1 supplies an independently checkable sufficient condition: choose rho(A)<lambda<1 and w=(I-A/lambda)^(-1)1, which is positive and satisfies Aw=lambda(w-1)<=lambda w. This is standard nonnegative-operator/small-gain reasoning, not a new termination theorem.

The alternating-token counterexample has A equal to a permutation matrix, rho(A)=1, and fails the criterion for a structural reason. Thus this mechanism genuinely detects the wiring obstruction that local termination misses.

### Dependence and adaptive scheduling

The local inequalities must hold conditionally for every admissible entry state/history, or after proving that the chosen state is a sufficient operational state. Fresh independent noise is NOT presumed. A hidden environment or scheduler can correlate subsequent calls; keep it in X_i or quantify uniformly over it.

For adaptive choices alpha, it suffices to establish a common positive w and lambda<1 with A^alpha w<=lambda w for every permitted choice, together with conditional local bounds. Separate stability of each choice is not sufficient: switching can defeat individual contraction witnesses. A controller's observation-dependent selection must be included before taking the relevant conditional expectation; unconditional marginal error/progress rates do not survive arbitrary selection.

The finite gain criterion is sufficient, not necessary. Additive or state-dependent drift can certify cases it misses; rejection by this certificate class is not incompatibility.

## 3. Operational transport lemma

For countable Q_X,Q_Y and a deterministic state map h:X->Y, an exact operational map satisfies

    Q_X h* = h* Q_Y,

where h*v=v composed with h. This is equality of the pushed-forward one-step continuation kernels, including continuation mass. It is much stronger than equality of final input/output behavior.

Pullback immediately preserves finite nonnegative additive certificates Q_Y V<=V-1, and multiplicative certificates V>=1, Q_Y V<=lambda V. More generally, a stochastic map H:X->Y with H1=1 and Q_X H=H Q_Y transports by V_X=H V_Y provided the resulting potential is finite. For substochastic H, H1=1 cannot be omitted when preserving the unit drift/lower bound.

For a surjective deterministic exact map e:G->R and a finite nonnegative certificate V_G, define

    e_! V_G(r) = inf { V_G(g) : e(g)=r }.

Set V_R=e_! V_G. Since e*V_R<=V_G, positivity and intertwining give, for every e(g)=r,

    Q_R V_R(r) = Q_G(e*V_R)(g)
               <= Q_G V_G(g)
               <= V_G(g)-1.

Taking the infimum proves Q_R V_R<=V_R-1. No minimum need be attained. Surjectivity ensures nonempty fibres and finite V_R. The identical proof preserves QV<=lambda V for lambda>=0; V>=1 is retained by infimum. For costs c_G, one gets the conservative pair V_R=inf V_G and c_R=inf c_G: Q_R V_R<=V_R-c_R. The derivation uses c_G(g)>=c_R(r), then takes infimum of V_G(g).

Therefore an operationally lifted comparison span

    X <-m- G -e-> R

with both legs deterministic exact kernel maps and e surjective sends an X-certificate to

    T_(m,e)(V)(r)=inf_(e(g)=r) V(m(g)).

No right inverse or functorial implementation selector is used. This avoids the previously proved no-functorial-section obstruction. These are ADDITIONAL operational properties of these legs; abstract E_0 does not mean surjective state map, and abstract M_0 does not mean an operational embedding.

One may weaken exactness of m to the appropriate positive-operator simulation inequality on the certificate family. Exactness of e is what lets the same R-transition expectation be compared with every representative. Any weaker version needs an explicit direction and proof, not a generic claim that simulation preserves termination.

## 4. Certificate composition and its exact limit

Given successive spans X<-G->Y and Y<-H->Z, form the full set fibre product

    P={(g,h): e_G(g)=m_H(h)}.

Then nested infima give the exact algebraic law

    T_H(T_G(V))(z)
      = inf_(e_H(h)=z) inf_(e_G(g)=m_H(h)) V(m_G(g))
      = T_P(V)(z).

Identities, reassociation, and state-relabeling coherence follow from the same equality of indexing sets. Right-leg surjectivity is stable under this set pullback. Disjoint unions give the evident componentwise law.

To transport PROGRESS as well as bare functions, P must carry an actual continuation kernel for which both projections intertwine. Existing joint operational data can provide it. On countable sets a conditional-product coupling can also be constructed when both marginals push forward to the same Q_Y: for matching successor images y', its mass is Q_G(g'|g)Q_H(h'|h)/Q_Y(y'|y), with zero assigned when the denominator is zero. Its projections have the prescribed marginals.

But this constructed coupling is not generally a categorical pullback of stochastic processes: different joint couplings have the same projections. Nor is it justified as the physical coupling of the original system. If the physical joint state space covers only a strict subset of compatible pairs, fibre-infimum composition can become an inequality rather than the displayed equality. Consequently the formal CFS mixed pullback does not automatically supply this operational construction or coverage.

This is the precise reconstruction gap: the prior theorem gives unique compatible FORMAL same-cylinder spans. It does not give transition kernels on their apexes, step-intertwining state maps, full set-pullback operational lifts, or a theorem that formal isomorphisms preserve those decorations. Certificate algebra is coherent once those data are established, but no claim that they follow from arbitrary CFS reconstruction has been proved here.

## 5. Why external cylinder equality is insufficient

A system that outputs b immediately and a system that outputs b after N hidden steps have exactly the same completed input/output kernel. All N are externally equivalent if elapsed time/steps are not among the tests. No fixed finite runtime certificate can therefore be inferred from that kernel alone. A geometric delay supplies a continuum of means with the same completed kernel; an almost-sure infinite-mean delay shows that even finite expected time is not an invariant of eventual-output semantics.

A formal realization may moreover not be a countable positive kernel system at all. The phrase 'transport through the canonical comparison' cannot repair this by treating the CFS middle as though it were already an operational state set.

A possible substantive next bridge is to prove a lift for a specified step-sensitive two-sided cylinder: tests must determine successor-state/continuation observations and admitted timing costs; reconstruction then has to produce a positive countable kernel and the actual comparison must satisfy the intertwining equations. Adding a tick test alone is not a proof. A general output-only reconstruction cannot satisfy the stronger step-preservation statement, as the delay example proves.

## 6. Contract accounting

Established here: a wiring-sensitive sufficient composition rule; an explicit dependence-aware operational span transport lemma; and exact certificate composition over genuine full state pullbacks. The quantitative drift and small-gain components are existing mathematics, imported rather than claimed novel.

Potentially useful new bridge in this program: fibrewise-infimum descent of progress along actual reconstruction spans, compatible with span composition without selecting an implementation. Novelty is unassessed; the formula is standard order-enriched existential/direct-image structure and must be compared with simulation/abstract-interpretation literature before claiming novelty.

NOT established: that the general free/native cylinder-factorization comparisons admit these operational lifts; that their formal mixed pullbacks agree with physical joint-state pullbacks; that arbitrary wiring preserves a common gain witness; or that arbitrary a.s.-terminating countable feedback admits a finite expected-time certificate. These are not cosmetic assumptions. They identify the remaining theorem rather than complete it by hypothesis.

## 7. Strengthening: a selected operational span bicategory DOES exist

The absence of a universal stochastic pullback does not prevent a coherent CHOICE of composition. The following strengthens section 4; it does not identify the chosen coupling with any physical coupling or with the free-CFS pullback.

Let objects be countable sets with substochastic continuation kernels Q. Arrows of the underlying operational category are deterministic exact intertwining maps. A span from X to Y is X<-m G-e->Y, with e surjective. Its apex has its own Q_G. A 2-cell is a deterministic exact intertwining apex map commuting with both legs. Endpoints of 2-cells are fixed.

For spans X<-G->Y and Y<-H->Z, choose the full set fibre product P=G x_Y H. For p=(g,h), p'=(g',h'), put y=e_G(g)=m_H(h), y'=e_G(g')=m_H(h'), and define

    Q_P(p'|p) = Q_G(g'|g) Q_H(h'|h) / Q_Y(y'|y)

when the denominator is positive, and zero otherwise. Every positive numerator has a positive denominator, by intertwining. Summing over h' with m_H(h')=y' cancels the denominator, so projection to G has exactly Q_G as its pushed-forward kernel. The other projection similarly gives Q_H. Hence Q_P is substochastic with correct marginal continuation mass, both projections intertwine, and the composite's right leg remains surjective. This is relative-independent coupling conditional on the next Y-state.

### Associativity and units

For three spans with apexes G,H,L and intermediate bases Y,Z, either parenthesization assigns the kernel

    Q_G(g'|g) Q_H(h'|h) Q_L(l'|l)
    / [Q_Y(y'|y) Q_Z(z'|z)]

to a compatible triple, with the common zero-denominator convention. Thus the canonical set associator is an exact kernel isomorphism. For the identity span on X, its factor Q_X cancels the denominator and the canonical unitor is an exact kernel isomorphism. The pentagon and triangle hold because they are the usual coordinate-rebracketing bijections, now proved operational. Disjoint unions are compatible with this composition because matching fibres stay in their disjoint summands.

### Horizontal 2-cells: fixed intermediate bases are essential

Suppose a:G->G' and b:H->H' are exact apex maps over the SAME X,Y,Z. The induced map a x_Y b on fibre products is well-defined. For fixed target successors (u',v'), its pushforward mass is

    [sum_(a(g')=u') Q_G(g'|g)]
    [sum_(b(h')=v') Q_H(h'|h)] / Q_Y(y'|y),

where y' is fixed by u',v' and the commuting endpoint maps. The two sums are Q_G'(u'|a(g)) and Q_H'(v'|b(h)) by intertwining. This is precisely the selected target coupling. Hence horizontal composition is well-defined on 2-cells. Functoriality, interchange, and naturality of the associator/unitors follow from the underlying fibre-product coordinate maps. This constructs a bicategory of selected operational spans; categorical pullback universality is not required.

The proof DOES NOT apply to arbitrary changes of the intermediate base Y. Coarsening Y generally mixes conditional laws and need not preserve relative independence. A doctrine-change/pseudofunctor theorem would require a separate base-change condition.

### Certificate semantics

For these spans, T_G(V)(y)=inf_(e(g)=y)V(m(g)) preserves the stated drift certificates. It sends span composition to exact function composition, and identities to identities. Associators and unitors leave it unchanged. For an arbitrary 2-cell a:G->G',

    T_G'(V) <= T_G(V),

because the image of each G-fibre is a subset of the corresponding G'-fibre. If a is surjective, equality holds; in particular operational apex isomorphisms give equality. Thus certificate semantics is naturally locally ordered (with reversed pointwise order for this 2-cell orientation), not a claim that every arbitrary apex map preserves the tight potential exactly.

### What this does and does not close

This closes an operational coherence construction: a concrete selected composition exists, has coherent comparison isomorphisms, and carries fibre-infimum progress certificates. It is stronger than merely saying 'assume an operational pullback'.

However, it does not yet close the reconstruction theorem. The original canonical CFS apex/middle still must be given positive countable kernels and exact deterministic legs with surjective right leg. The selected product coupling is not automatically the original physical joint coupling. If a physical coupling on the SAME full fibre-product state set has the same exact projections, the certificate transport proof remains valid independently of its correlations; numerical drift bounds require only those projections. But its kernel need not be isomorphic to the selected one, so this fact does not identify all physical couplings categorically.

This operational span construction and its relation to probabilistic bisimulation spans/disintegration should be literature-checked before novelty claims. The new mathematical work here is the explicit construction and verification for the present progress-transport interface, not a claim that relative-independent Markov couplings were previously unknown.
