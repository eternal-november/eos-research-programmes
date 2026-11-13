# Witness-preserving gluing: exact obstruction and cost examples

These are finite constructions, not novelty claims. They distinguish preservation of observed laws, preservation of chosen local mechanisms, and resource-preserving implementation.

## 1. A shared state law is not a shared state mechanism

Take one announcement, shared retained state set S={0,1}, and Q=I. Local model 1 has a singleton hidden state, initial weight A1=[1], and retained-state kernel B1=[1/2,1/2]. Local model 2 has two hidden states, A2=[1/2,1/2], B2=I2. Both induce T=[1/2,1/2].

Suppose a joint source is required to retain the local hidden states through deterministic projections f_i and to commute with the *same* retained-state link B. Every used source state v must satisfy B(v,-)=B1(f1(v),-)=B2(f2(v),-). No row of B2 equals the unique row of B1. Hence no such source exists, at any cardinality. An ordinary joint distribution on S,H1,H2 does exist: take S fair, H1 constant, H2=S. It fails the required statewise comparison square because conditioning on H2 changes the law of S.

Allowing stochastic comparisons changes the answer: a one-state source with B=[1/2,1/2] and C1=[1], C2=[1/2,1/2] satisfies C_i B_i=B and A C_i=A_i. Thus deterministic occurrence retention must not be silently replaced with randomized comparison.

For arbitrary fixed local objects (A_i,B_i) with common announcement J and common retained S, deterministic common covers exist exactly when, for every j, the pushforward weights A_i(j,-) along h_i -> B_i(h_i,-) agree as measures on the set of distinct kernel rows. Necessity follows from commuting squares. Sufficiency couples the local states independently conditional on the shared kernel profile. This criterion concerns equality of complete link kernels, not equality after multiplying by an output channel Q.

By contrast, stochastic common sources exist exactly when all A_i B_i coincide. Necessity is immediate from A C_i=A_i and C_i B_i=B. For sufficiency, put p_j=sum_h A_i(j,h), take A=diag(p), C_i(j,h)=A_i(j,h)/p_j, and B(j,s)=T(j,s)/p_j, omitting zero-mass j if needed. Consequently a general claim of existence for stochastic common sources at a fixed full coupling T would be automatic in this finite setting.

## 2. Correlation memory forces arbitrarily many splits of one hidden tuple

Let m>=2. There are two local modules, each with one hidden state and a uniform output in Z_m. The announcement set is J=Z_m, with p_j=1/m. Each local root matrix is A_i(j,*)=1/m, and each local continuation kernel is B_i(*,x)=1/m. Let the joint retained carrier be S=Z_m x Z_m, with Q=I and w(x,y)=1/m^2.

For 0<=epsilon<1 define the joint conditional continuation law

    beta_j(x,y) = (1-epsilon)/m * 1[y=x+j mod m] + epsilon/m^2,
    R(j,(x,y)) = beta_j(x,y)/m.

All beta_j have uniform local marginals, and their average is w. Therefore the joint law preserves both chosen local mechanisms and their deterministic projections from any joint latent state to the singleton local hidden states.

Nevertheless the one available hidden tuple cannot implement R: its single continuation kernel cannot depend on j. Exactly m joint middle states are required. The upper bound uses A=diag(1/m) and B(j,-)=beta_j. For the lower bound, let D have rows equal to the uniform laws on the m disjoint matchings y=x+j. Then B=C D, where

    C=(1-epsilon) I_m + (epsilon/m) 11^T.

D has row rank m and C has eigenvalues 1 and 1-epsilon. Thus R has ordinary rank m, so every nonnegative factorization and every phase-tagged native implementation has at least m middle states. This is a resource obstruction even when epsilon=1/2 makes every joint outcome positive in every announcement context.

The total phase-tagged state cost is m+2, while each local model has cost 3. The growth comes from correlation memory that neither local model needs. It is not caused by a larger local hidden-state tuple, impossible local marginals, or zero probabilities.

## 3. Cycle obstruction can live entirely in retained interfaces

Let X,Y,Z be fair binary interface variables. Prescribe pair distributions for XY,YZ,XZ. XY and YZ favor equality, while XZ favors inequality. In the sharp version, each favored pair receives probability 1/2 and the other pairs probability zero. All single-variable overlap laws agree, but no joint law exists: X=Y and Y=Z imply X=Z.

A full-support version places 9/20 on each favored pair and 1/20 on each other pair. Each favored relation then has probability 9/10. Pointwise, at most two of the three relations X=Y, Y=Z, X!=Z can hold. A joint law would therefore satisfy

    Pr[X=Y]+Pr[Y=Z]+Pr[X!=Z] <= 2,

whereas the prescribed laws give 27/10. This is a direct dual obstruction certificate. All pair laws have full support and all overlap marginals agree.

If each component's public output channel is constant, every observable component and the whole observable system admit the trivial one-output realization. The obstruction remains only because the pairwise retained interface laws must be preserved. This is a standard marginal-extension/contextuality obstruction placed at the native interface level, not a new obstruction principle.

## 4. Tree gluing does not make an arbitrary global correlation canonical

For fair X,Y,Z, suppose the specified edge marginals XY and YZ are independent. The conditionally independent tree gluing gives three independent bits. Another joint law takes X=Z fair and independent of Y. Both preserve the supplied edge marginals. Thus an associative selected Markov gluing can be justified, but uniqueness of all admissible global realizations cannot be inferred from tree overlap consistency. Any coherence theorem must state whether it compares the selected gluing, all gluing witnesses, or already specified higher correlations.

## Interpretation for the construction

The joint-state formulation with S a subset of a product of local retained states permits coupling local link kernels. The strict shared-S example is recovered by taking S to be the diagonal subset: a coupling supported on that diagonal exists exactly when the local kernel rows agree. The correlation-memory example instead uses the full product S, where row coupling is easy but implementing distinct announcement-dependent couplings requires splitting the same local hidden tuple.
