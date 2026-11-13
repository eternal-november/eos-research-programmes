# Exact checks and counterexamples for the fixed-budget encoding

These are mathematical calculations for the polynomial encoding proved in `report.tex`. They do not require numerical optimization. Every claim distinguishes failure of a solver from failure of the realization problem.

## 1. The all-inactive point is stationary and infeasible

For slot v, use selectors d_vh, activity e_v=sum_h d_vh, root weights a_jv=rho_jv^2, and continuation entries b_vs=tau_vs^2. The structural residuals include

- d_vh^2-d_vh;
- 1-e_v-eta_v^2;
- a_jv-rho_jv^2;
- e_v-a_jv-sigma_jv^2;
- b_vs-tau_vs^2;
- sum_s b_vs-e_v;
- the homogeneous local-marginal equations for b and d.

The data residuals contain products a*d for retained initial laws and a*b for the joint prior and output law.

Set every d,a,b,rho,sigma,tau to zero and every eta to one. All structural residuals vanish. All data residuals are negatives of their supplied targets, but the derivative of each product a*d or a*b vanishes at this point. Hence the full objective has gradient zero. Its value is

  sum_i ||A_i||_F^2 + ||w||_2^2 + ||R||_F^2 > 0

when these data constraints are included. Positive normalization of the initial law makes the point infeasible. Gradient flow or fixed-step gradient descent initialized there remains there. This applies to the unweighted encoding itself, without any added circle variables. It also survives positive weighting of residuals.

## 2. A genuine strict positive local minimum in a feasible instance

This is a counterexample for the same exact encoding with a legitimate positive choice of residual weights. It is not a claim that the unweighted singleton objective has the same strict local minimum.

Take all sets J,E,S,I and the local hidden carrier singleton, budget one, and A=w=R=1. Write one slot's coordinates as (d,a,b,rho,sigma,tau,eta). The structural residual list is

  d^2-d,
  1-d-eta^2,
  a-rho^2,
  d-a-sigma^2,
  b-tau^2,
  b-d,
  b-d.

The last two copies are the continuation normalization and the singleton local-marginal equation. Keeping only one copy also works for the proof below.

Define

  F = 100 * sum(structural residuals squared)
      + (ad-1)^2 + 2(ab-1)^2.

The three data constraints are retained initialization, prior, and output. Positive residual weights leave the exact zero set unchanged. This is still a quartic polynomial sum of squares on an ordinary Euclidean space.

At

  P0=(0,0,0,0,0,0,1),

F=3 and its full gradient is zero. At

  P1=(1,1,1,1,0,1,0),

F=0. Thus the underlying realization is feasible with one state.

Here is an exact proof that P0 is a strict local minimum. Put

  L=a-rho^2, G=d-a-sigma^2, N=b-d.

For |d|<1/2, (d^2-d)^2 >= d^2/4. Since rho^2 and sigma^2 are nonnegative,

  a^2 <= 2d^2 + 2G^2 + L^2.

Indeed, for a<0, a^2<=L^2; for a>=0, a<=|d|+|G|. Also b^2<=(2d^2+2N^2). The data contribution satisfies

  (ad-1)^2+2(ab-1)^2-3
  = a^2 d^2 + 2a^2 b^2 - 2ad - 4ab
  >= a^2 d^2 + 2a^2 b^2 - d^2 - 3a^2 - 2b^2.

Consequently

  F-3 >= 14d^2 + 94G^2 + 97L^2 + 96N^2
          + a^2 d^2 + 2a^2 b^2
          + all remaining nonnegative structural terms.

Equality requires d=L=G=N=0, hence a=b=rho=sigma=0; the remaining square-link residual forces tau=0, and the cap forces eta^2=1. In a neighborhood of eta=1 this is exactly P0. Therefore P0 is a strict local minimum with positive objective although a zero exists.

Independent symbolic verification with SymPy gave F(P0)=3, F(P1)=0, and all seven partial derivatives zero at P0. The Hessian in the nonflat coordinates (d,a,b,eta) is

  [[1000,-202,-400,400],
   [-202,400,-4,0],
   [-400,-4,600,0],
   [400,0,0,800]].

Its leading principal minors are 1000,359196,150855200,82286720000. The full Hessian is semidefinite, with flat rho,sigma,tau directions; the inequality above, not the Hessian alone, establishes strict local minimality.

## 3. Empty coupling polytopes must not invalidate unused slots

Take J singleton; H1=H2={0,1}; Ai=(1/2,1/2); Bi=Id_2. Let S={0,1}, with both local coarse projections identity, E=H1 x H2, Q=Id, and w=R=(1/2,1/2).

Then

  K_(0,0)={delta_0}, K_(1,1)={delta_1},
  K_(0,1)=K_(1,0)=empty.

A two-state realization uses tags (0,0) and (1,1), root weights 1/2 each, and continuation rows delta_0 and delta_1. Every local hidden state has positive initial mass, so this is not caused by a globally unused local state.

If a fixed per-tag capacity assigns one possible slot to each of the four tags, requiring every padded continuation row to lie in its K_h falsely declares infeasibility. The two off-diagonal slots must be allowed to be inactive. Correct activity encoding has d=a=b=0 in each such unused slot, eta=1, rho=sigma=tau=0. One can instead remove empty K_h before constructing a per-tag formulation.

For entirely rational amplitude checks replace (1/2,1/2) everywhere by (9/25,16/25). The active root amplitudes are 3/5 and4/5; their gate-slack amplitudes are 4/5 and3/5. The same empty-polytope conclusion holds.

## 4. Linear compatibility does not settle a fixed state budget

Take two singleton local hidden carriers, both local continuation laws uniform on {0,1}; J={0,1}; each Ai(j)=1/2; E singleton; S={0,1}^2; Q=Id; and w uniform on the four joint outputs. In column order (00,01,10,11), let

  R = [[1/4,0,0,1/4],
       [0,1/4,1/4,0]].

The linear coupling problem is feasible, with its unique certificate block Z=R. The minor on columns00,01 is1/16, so rank(R)=2. Any one-state factorization has ordinary rank<=1, hence budget one is impossible. Two states suffice, with root weights (1/2,0) and(0,1/2) and continuation rows (1/2,0,0,1/2), (0,1/2,1/2,0).

This obstruction survives full support. Replace R by

  R_full = [[3/16,1/16,1/16,3/16],
            [1/16,3/16,3/16,1/16]].

Its same minor is1/32. Both local output marginals remain uniform, w remains uniform, all joint outcomes are positive, and the exact minimum remains two states.

## 5. Arbitrarily small residuals do not give a uniform exact-feasibility test

Fix any epsilon with0<epsilon<1. Take J singleton, H1=H2={0,1}, Ai=(1/2,1/2), E={(0,0),(1,1)}, and shared S={0,1} with both projections identity. Put

  B1(0)=(1,0), B1(1)=(0,1),
  B2(0)=(1-epsilon,epsilon),
  B2(1)=(epsilon,1-epsilon).

Let Q=Id and w=R=(1/2,1/2). All aggregate local observed distributions and the global targets agree. Nevertheless both allowed K_h are empty: a shared continuation row would have to equal two different specified probability vectors. No realization exists at any budget.

For a two-slot approximate point, select the two allowed tags, give each root weight1/2, and use continuation rows

  b0=(1-epsilon/2,epsilon/2),
  b1=(epsilon/2,1-epsilon/2).

All initialization, normalization, gate, prior, output, and nonnegativity residuals vanish. Only the four local-row matching equations (with their two coordinates each) fail. Their total squared residual is exactly2*epsilon^2. Thus the unweighted objective can be arbitrarily small on infeasible instances, even though ordinary aggregate validation passes.

This varies the input instance. It does NOT show infimum zero without a zero for one fixed instance. For the proper coercive encoding, every fixed infeasible instance has a strictly positive attained global minimum. No data-independent floating-point tolerance can distinguish all these positive minima from zero.

## 6. Boundary parameterizations and omitted bounds can create separate traps

These are cautions about alternatives, not counterexamples to the proposed bounded/coercive polynomial encoding.

- Strictly positive/softmax parametrizations miss genuine boundary solutions. To realize delta_0, set beta(t)=(e^t/(1+e^t),1/(1+e^t)). Its squared distance to(1,0) is2/(1+e^t)^2. The infimum is zero, approached as t goes to infinity, but no finite parameter attains it. Squares allow zero entries and avoid this exclusion.
- Without bounding/normalizing the factor variables, even a polynomial residual can have unattained infimum zero: G(a,b)=(ab-1)^2+a^2 on a,b>=0. There is no zero, but G(1/n,n)=1/n^2. Its fully squared-parameter version is (u^2v^2-1)^2+u^4 with value1/n^4 at(u,v)=(1/n,n). The activity gates and row-normalization bounds in the actual encoding rule out this escape.

## 7. Independently optimal local choices need not have a common witness

Let X,Y,Z be unbiased binary variables, with otherwise unconstrained joint couplings. The selected pairwise witnesses may be

  P_XY(00)=P_XY(11)=1/2,
  P_YZ(00)=P_YZ(11)=1/2,
  P_XZ(01)=P_XZ(10)=1/2.

Each pair is individually valid, retains its two singleton local mechanisms, and can be an exact zero/minimizer of its pairwise fitting objective. The shared single-variable marginals all agree. But any global witness would satisfy X=Y andY=Z almost surely, hence X=Z almost surely, contradicting the last pair. Equivalently,

  P(X != Z) <= P(X != Y)+P(Y != Z)

would read1<=0.

The original three individual unbiased local mechanisms do admit global witnesses (for example independence). It is the independently chosen intermediate correlations that cannot all be retained. Summing/wiring objectives preserves their common zero set, not the compatibility of arbitrarily selected individual minimizers, and supplies no automatic associator between those choices.
