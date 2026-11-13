# Finite qualitative execution with divergence: an exact quotient without a functorial lift

Research derivation / independently checked companion, 2026-10-30.

## Setting and theorem

Work with finite sets and substochastic matrices K:B×A→[0,1], column sums at most1; composition is matrix multiplication. Tensor is disjoint union, NOT Cartesian product. Its operational feedback is first exit, NOT compact matrix trace. Empty sets are allowed. The symbol 1 below is a singleton set, not the disjoint-union tensor unit (which is the empty set).

**Theorem.** Support together with positive-missing-mass per input is a surjective, identity-on-objects quotient of finite substochastic execution semantics. It preserves composition, disjoint union, and first-exit feedback exactly; it reflects normalized stochastic admission after any finite feedback context. It is contextually complete for support and per-input normalization observations. Nevertheless the quotient admits no functorial section, even when feedback preservation is not requested.

Write a feedback kernel f:A+U→B+U in blocks R:A→B, S:A→U, T:U→B, Q:U→U. Define

    Tr_U(f)=R+Σ_(n≥0) T Q^n S.

Each summand is the mass of paths first exiting to B after a specified number of internal transitions. These events are disjoint, so the series converges entrywise to a substochastic matrix. Q may have eigenvalue1; an inverse (I−Q) is neither needed nor asserted.

The trace laws follow from path partitions: naturality adds an external prefix/suffix; dinaturality changes the chosen cut in alternating internal paths; vanishing over two hidden sets partitions a path into maximal excursions through either one; superposing preserves the separate component; yanking leaves exactly the direct matching path. Nonnegative countable sums permit each regrouping by Tonelli, so no convergence cancellation is hidden. This is the standard first-exit execution trace, stated here to fix the actual operational meaning.

## 1. A repaired qualitative quotient that survives black-boxing

For a finite substochastic kernel K:A->B define J(K)=(R_K,D_K), where R_K(a,b) iff K(b|a)>0, and D_K={a:sum_b K(b|a)<1}. D records positive probability of missing mass, not its size. Feasible pairs are exactly those for which an input with empty R-fibre belongs to D. Each is realized: distribute total mass 1 uniformly over each nonempty fibre for a not in D, total mass 1/2 for a in D, and mass 0 over empty fibres.

Composition has exact law

    R_(g f) = R_g R_f,
    D_(g f) = D_f union {a: exists b, R_f(a,b) and b in D_g}.

Indeed delta_(gf)(a)=delta_f(a)+sum_b f(b|a) delta_g(b), all terms nonnegative. Disjoint-union tensor takes disjoint unions of R and D; identities have diagonal R and empty D.

For first-exit feedback of f:A+U->B+U, R is finite-path reachability. An input a belongs to the feedback D iff either:

1. A locally deficient input vertex is reachable: a itself lies in D_f, or some u in D_f is reachable from a through internal support edges; or
2. From a one can reach a nonempty internal support-closed communicating class: an SCC of U with no support edge to B or to another internal SCC.

Reachability of a local deficit gives positive missing mass along a finite path. A reached closed class either has a reachable deficit (already case1) or preserves all mass forever, giving nontermination. Conversely, absent both cases, the reachable subgraph is locally normalized and every reachable internal vertex has a positive path to B. For completeness: choose from each reachable internal vertex a simple positive path to B of length at most |U|. There are finitely many such choices, so the minimum epsilon of their path-probability products is positive. From every reachable internal state, the probability of exit in the next |U| steps is at least epsilon. Survival after k such blocks is at most (1−epsilon)^k, which tends to0. If U is empty there is no hidden iteration. Therefore D of feedback is determined by R_f,D_f alone.

Consequently equality of J-images is a congruence for ordinary composition, disjoint union, and finite first-exit feedback. This is stronger than keeping an unhidden full graph forever: after computing feedback the new external pair (R,D) can itself be substituted in any further such operation. Given the first-exit traced structure of finite substochastic kernels, quotient descent supplies the trace laws, rather than having to guess an abstract guard axiom.

Relative contextual completeness: if observations consist of supports and per-input normalization, then equality of (R,D) is preserved by all such contexts, while any difference in R or D is already directly observable (D at a chosen input can be observed by precomposing the deterministic point a and discarding the output). Thus (R,D) is the coarsest support-refining quotient that retains these observations. This is not completeness for numerical safety thresholds, probability estimates, expected-time bounds, or arbitrary additional observations.

## 2. Surjective realizability is NOT a functorial lift

There is no identity-on-objects functor S from the feasible-pair quotient back to finite substochastic kernels satisfying J S=id. The obstruction already lies in the D=empty total-relation subcategory, without feedback or tensor preservation requirements.

Let R:1->{1,2} be the total two-output qualitative map. Any section must choose S(R)=p=(r,1-r)^T with 0<r<1. Let g:{1,2}->{1,2} have first column R, second column the deterministic point1, and no deficient input. The deterministic point maps have unique lifts. Functoriality of S under precomposition with these points therefore forces

    S(g) = [[r,1], [1-r,0]].

Qualitatively g R=R. Functoriality would require S(g)p=p. Its first component requires r^2+1-r=r, hence (r-1)^2=0, contradicting 0<r<1.

So every qualitative object/morphism has a concrete realization and the quotient has exact coherent composition/feedback/admission, but no global composition-preserving choice of stochastic representatives exists. The uniform per-fibre realization in section 1 is a set-theoretic witness of surjectivity, not a functor. This is a genuine lifting obstruction, not a failure of the forward quotient and not a claim that individual compatible stochastic implementations cannot be designed.

## 3. Why divergence is needed, and what the repair does not retain

For A={a}, B={b}, U={u}, consider a→(1/2)b+(1/2)u, u→u. All local columns are normalized. First exit is the scalar1/2, so the external D is {a}; external support is the total singleton relation. Compare a→u, u→(1/2)b+(1/2)u: first exit is1, hence external D is empty, although external support is again total. Plain relational may-totality cannot distinguish these black boxes; J can. An infinite graph path in the second system has probability0, so requiring termination along every possible graph path would be strictly stronger than almost-sure termination.

Support of feedback is exactly relational finite-path feedback:

    supp Tr_U(f) = supp R ∪ supp T (supp Q)* supp S.

This holds because a nonnegative countable sum is positive iff some summand is positive. Failure of plain support to retain normalization is therefore not a failure of this algebraic support law.

J observes whether missing mass is positive, not how much. Kernels with exit probability0.01 and0.99 can have identical J. Similarly loops with positive exit probability epsilon and the same support have expected exit time1/epsilon, arbitrarily large as epsilon decreases. The quotient does not retain numerical safety budgets, uniform time bounds, or probability-sensitive behavior.

### No continuity claim for the deficit flag

J does not preserve increasing limits: scalar kernels p_n=1−1/n have D=true for every finite n, whereas their limit1 has D=false. In the geometric leaky-loop example, each finite partial exit sum is strictly below1 and hence deficient, but the infinite first-exit sum is1 and is not deficient. Accordingly the quotient trace is derived from the finite-state reachability/SCC theorem; it is NOT obtained by naively taking a union of finite-unfolding (R,D) summaries, and no preservation of countable sums or omega-continuity by J is claimed. Only the support component has the countable positivity law used above.

## 4. Finiteness is essential: identical J, different feedback deficiency

Allow countably many hidden states U={1,2,...}, one input a entering state1 deterministically, and one output b. At internal n≥2, move down to n−1 with probability p and up to n+1 with probability q=1−p. At n=1, the down move exits to b and the up move goes to2. For every 0<p<1, the unhidden kernel has exactly the same support and no deficient local column.

Let h_i^N be the probability of hitting0 before N for the ordinary walk on {0,...,N}, started at i. It satisfies

    h_0^N=1, h_N^N=0,
    h_i^N=p h_(i−1)^N+q h_(i+1)^N.

For p≠q, solving this finite recurrence gives

    h_i^N=((p/q)^i−(p/q)^N)/(1−(p/q)^N).

The events of hitting0 before N increase with N, and their union is hitting0 in finite time: each path hitting0 has a finite maximum before that hitting time. Thus their probabilities converge to the eventual exit probability. At i=1 this limit is p/q when p<q and1 when p>q. Consequently p=1/3 gives exit mass1/2, while p=2/3 gives exit mass1.

Both open kernels have identical (support,D=empty), but feedback yields different D. Therefore J is NOT a trace congruence for the countably infinite class. Every hidden vertex has a finite support path to exit in both cases; finiteness was what supplied a uniform positive progress bound. This boundary matters if a canonical realization introduces infinitely many states. The finite theorem must not be transported to that realization without another progress hypothesis or richer semantics.

## 5. Explicit connection to free cylinder reconstruction

Let C=FinSubStoch and D=QualDiv denote the categories of finite systems just constructed, with disjoint-union first-exit traces, choosing finite-set skeletons to ensure smallness. The derived J:C→D is strong symmetric monoidal and trace-preserving. Functoriality of the Joyal–Street–Verity Int construction therefore supplies a compact-closed strong monoidal functor H=Int(J):Int(C)→Int(D). Concretely, H applies J to the underlying execution morphism between the signed interfaces; preservation of Int composition follows from the proved first-exit trace law. This is an application of [Joyal–Street–Verity, *Traced monoidal categories*](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/abs/traced-monoidal-categories/2BE85628D269D9FABAB41B6364E117C8), not a new Int theorem.

Apply the free Isbell/CFS construction to H. For every specified small cylinder r in Int(C), the main cross-doctrine theorem gives the exact canonical comparison

    I(H) R_free,Int(C)(r) ≅ R_free,Int(D)(H r).

It also transports the actual canonical normalization comparison spans, including their mixed-pullback compositors. Because H preserves the compact wiring operations, the existing fixed-port joint-cylinder assembly and wiring coherence apply to these translated cylinders. Thus this companion is not merely a candidate example: it supplies an operationally derived traced translation that feeds into the established free reconstruction comparison. The free-CFS infrastructure is [Garner, *The Isbell monad*](https://arxiv.org/abs/1410.7108); the explicit comparison and span consequences are those proved in cross_doctrine_comparison_theorem.md and the preceding structural checkpoint.

The passage through Int and I is a FORMAL completion. It does not equip QualDiv itself with a native CFS, choose stochastic representatives, make canonical realization objects finite or operationally implementable, or extend the finite normalization-reflection theorem to arbitrary completion objects. On original finite kernels, including after any finite first-exit context, the already proved operational admission test remains exact: the resulting kernel is normalized iff its J-image has empty deficit set. In particular, for an original stochastic f:A+U→B+U, its first-exit feedback is again stochastic iff the feedback pair has D=empty. No such admission claim is inferred for arbitrary formal cylinders or infinite canonical states.

The no-section theorem prevents turning this forward comparison into a globally coherent choice of stochastic implementation. The countable random-walk counterexample prevents extending the finite admission guard to infinite canonical realizations without extra progress information.

Finally, the execution trace here uses disjoint union. Compact trace over Cartesian-product matrix interfaces is a different operation; the identity on a two-state hidden object has compact matrix trace2, not an instance of the first-exit counterexamples above. The compact structure introduced by Int is the formal one generated from the execution trace, not an identification of those two matrix operations.
