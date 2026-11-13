# Exact-rational executable checks

This directory checks the actual ten-family fixed-budget slot encoding, not only an abstract sum-of-squares example. It uses Python 3's standard library only, with `fractions.Fraction` for all arithmetic. No float or numerical optimizer is used. Every test uses an explicit comparison and raises on failure; none depends on a Python `assert` statement.

## Reproduce

From this directory, run `./run_checks.sh`. The wrapper runs both commands below and compares the mathematical JSON reports after excluding only the optimization-level field:

```
python3 run_checks.py --json results_normal.json
python3 -O run_checks.py --json results_optimized.json
```

Both final runs passed **203 exact-rational checks**, including **341 exact native-generator cylinder calculations through word length four** (reported as one aggregate check). The two modes give identical mathematical results. Optimization levels are recorded separately. `python3 -m py_compile exact_polynomial.py native_encoding.py run_checks.py` also passed.

- `exact_polynomial.py`: a small sparse polynomial implementation over rational coefficients, symbolic differentiation and substitution, an independent residual-Jacobian gradient calculation, and exact evaluation using rational squares of algebraic slack coordinates.
- `native_encoding.py`: input checks; the exact residual families D,H,P,G,T,N,C,L,W,O; rational square-root lifting for chosen examples; exact-zero decoding; and three finite native input instances.
- `run_checks.py`: reproducible tests and optional JSON reporting.
- `run_checks.sh`: ordinary/optimized runner and exact report comparison. Each run checks explicit expected values and polynomial identities in the source; the saved report is not an independent oracle.
- `results_normal.{txt,json}` and `results_optimized.{txt,json}`: saved outputs of the two successful runs.

## Exact encoding convention

For K middle-state slots, variables are d[v,h], eta[v], a[j,v], rho[j,v], sigma[j,v], b[v,s], tau[v,s]. The activity e[v] is the sum of selectors d[v,h], not a separate coordinate. Residuals are:

```
D[v,h] = d[v,h]^2 - d[v,h]
H[v] = 1 - sum_h d[v,h] - eta[v]^2
P[j,v] = a[j,v] - rho[j,v]^2
G[j,v] = sum_h d[v,h] - a[j,v] - sigma[j,v]^2
T[v,s] = b[v,s] - tau[v,s]^2
N[v] = sum_s b[v,s] - sum_h d[v,h]
C[v,i,x] = sum_{s:s_i=x} b[v,s] - sum_h d[v,h] B_i[h_i,x]
L[i,j,u] = sum_v a[j,v] sum_{h:h_i=u} d[v,h] - A_i[j,u]
W[s] = sum_{j,v} a[j,v] b[v,s] - w[s]
O[j,u] = sum_{v,s} a[j,v] b[v,s] Q[s,u] - R[j,u]
```

The default objective is the unweighted sum of every scalar residual square once, with no one-half factor. Formally different residuals that coincide as polynomials are retained separately. In particular, the singleton N and C residuals both equal b-d and both appear.

The implementation follows the section-ready construction in `../encoding_derivation.tex`. Tests check all residual values at witnesses, then independently decode and verify the native root, continuation, retained, and observable equations. All example output kernels Q are identities. Their local output kernels can also be identities and their local output maps the retained-coordinate projections, so the statewise output-comparison squares are identities.

## Coverage and exact outcomes

### 1. A feasible native instance and a false stationary solution

The singleton input has A=B=Q=w=R=1 and K=1. The active point has d=a=b=rho=tau=1 and sigma=eta=0, and every residual vanishes. Its native implementation has one middle state and three total states.

The all-inactive point has d=a=b=rho=sigma=tau=0 and eta=1. Its objective is exactly 3 and all seven partial derivatives are exactly zero. The script checks both the differentiated expanded objective and the formula 2 J_F^T F. A further nonstationary rational point checks that the gradient implementations agree away from zero.

For K=0 there are no variables and the singleton objective is the constant 3.

### 2. A strict positive local minimum with positive residual weights

On the same feasible singleton instance, give the seven structural residuals weight 100 and each of the three data residuals weight 1. The zero set is unchanged. The all-inactive point is stationary at value 3, while the active point has value 0.

The code verifies the exact polynomial identity behind the strict-local-minimum proof, not just a sampled numerical Hessian. With D=d^2-d, H=1-d-eta^2, L=a-rho^2, G=d-a-sigma^2, T=b-tau^2 and N=b-d, set

```
B = 14 d^2 + 94 G^2 + 97 L^2 + 96 N^2 + a^2 d^2 + 2 a^2 b^2.
```

For the weighted objective F, the exact identity checked is

```
F - 3 - B
 = 100 (D^2-d^2/4)
   + (a-d)^2 + 2(a-b)^2
   + 3(2d^2+2G^2+L^2-a^2)
   + 2(b-2d)^2 + 100(H^2+T^2+N^2).
```

Every right-hand term is nonnegative when |d|<1/2. For the only non-obvious term, if a<0 then L=a-rho^2<=a and L^2>=a^2; if a>=0, then a=d-G-sigma^2<=d-G, whence a^2<=2d^2+2G^2. Equality forces d=L=G=N=0, hence a=b=rho=sigma=0, then tau=0 and eta^2=1. In a neighborhood of eta=1, the equality point is exactly the all-inactive point. This proves a strict positive local minimum for this weighted objective. The claim is not made for the unweighted singleton objective.

The nonflat Hessian block also agrees exactly with the independent derivation. The full Hessian has flat square-slack directions, so the Hessian alone would not establish strict local minimality.

### 3. Empty coupling polytopes and harmless unused slots

There are two modules, each with H_i=S_i={0,1}, B_i=Id, one announcement, and A_i=(9/25,16/25). The joint retained carrier is the diagonal S={(0,0),(1,1)} and E contains all four hidden pairs. Q=Id and w=R=(9/25,16/25).

The diagonal tags have continuation rows delta_0 and delta_1. The two off-diagonal tags have empty coupling polytopes. A four-slot witness occupies only two slots, with diagonal tags and root amplitudes 3/5 and 4/5. Every coordinate and slack is rational; every residual is zero. The unused slots have zero continuation rows, not normalized probability rows.

If a slot is forced to select (0,1), its two local x=0 residuals differ identically by -1. The code verifies that polynomial contradiction. This shows why mandatory normalized padding for every tag would introduce a false obstruction.

The decoded four-total-state native generator is built explicitly. All 341 words over its four-symbol alphabet through length four have the exact prescribed cylinder probabilities, including zero probability for forbidden phase patterns.

### 4. Linear compatibility but impossible one-state budget

Both modules have one local hidden state and four local retained states, with uniform local continuation rows. The joint retained carrier is {0,1,2,3}^2 and E is singleton. There are two announcements with probabilities p=9/25 and q=16/25. Conditional on the first, the joint state is uniform on the diagonal; conditional on the second, it is uniform on the cyclic shift {(0,1),(1,2),(2,3),(3,0)}.

Two middle states give a full exact-rational zero of all 114 residuals in 80 variables. All continuation probabilities are 0 or 1/4, so their square roots are 0 or 1/2. The root amplitudes and complement amplitudes are rational as well.

The linear compatibility tensor is R itself. Its mechanism equations are checked exactly. Its minor on retained columns (0,0) and (0,1) is 9/625. Every corresponding 2-by-2 minor from a one-state factorization vanishes as a symbolic polynomial. Therefore one middle state is impossible, while two suffice. This is an exact rank obstruction, not a failed optimizer or a claim inferred from a positive local residual.

This four-state-per-module variant is used so the full slack witness is rational. It serves the same purpose as the smaller binary rank-two example in the main mathematical discussion.

### 5. Wiring, shared gradients, and Euler transport

Two residual components share a coordinate. The exact local derivative contributions are -1/3 and -1/3; the assembled derivative is their sum -2/3. A synchronized Euler step of size 1/10 sends the shared coordinate from 1/3 to 2/5.

For the duplicated-coordinate map phi=(1,1)^T, y=3, and local update U(x)=(3/4)x, naive transport phi^T U(phi y) gives 9/2. Euler after assembling the vector field gives 3/2. Correct increment transport

```
T_phi(U)(y) = y + phi^T (U(phi y)-phi y)
```

gives 3/2. Naive transport sends the identity update at y=3 to 6; increment transport preserves it at 3. The corrected transport's identity and composition laws are also checked on explicit arbitrary rational linear maps and a nonlinear polynomial update.

These checks show the Euler naturality/baseline issue. They do not claim that naive conjugation is itself nonfunctorial under composition of linear maps; the failure is its incompatibility with the intended Euler baseline and with identifying the wired identity dynamics as the identity update.

### 6. Coercivity controls

Six rational points, including the exact zero and the false stationary point, are checked against the construction's explicit sublevel coordinate bounds. To keep all calculations rational, choose epsilon=q(q-1), so D_epsilon=(1+sqrt(1+4 epsilon))/2=q exactly. These examples test the bound formulas; the general coercivity theorem is proved in the mathematical note, not inferred from finitely many points.

For the optional redundant circle completion, the script checks the polynomial identity

```
N sum_i u_i^2 - (sum_i u_i)^2 = sum_{i<j}(u_i-u_j)^2,
where u_i=x_i^2+z_i^2-1.
```

This is the exact Cauchy-Schwarz lower bound used in its coercivity proof. Finally the ungated polynomial (ab-1)^2+a^2 is evaluated at (a,b)=(1/n,n), giving 1/n^2 for n=1,2,5,10,100. That separate example explains why generic polynomial sum-of-squares attainment cannot be assumed.

### 7. The infeasible family with loss exactly 2 epsilon squared

The binary shared-state family has one announcement, A_1=A_2=(1/2,1/2), diagonal E and S, B_1=Id, and B_2 rows (1-epsilon,epsilon) and (epsilon,1-epsilon). Its aggregate retained and observed targets are (1/2,1/2), so the cheap input checks pass. Every allowed coupling polytope is empty: after selecting a tag, the two local x=0 row residuals differ by either +epsilon or -epsilon. The code verifies those constant polynomial contradictions.

The approximate two-slot point has root weights 1/2, selectors on the two diagonal tags, and continuation rows (1-epsilon/2,epsilon/2) and its reversal. Exactly eight C residuals are nonzero, each with magnitude epsilon/2. Every other residual is zero, and the full encoded objective is exactly 2 epsilon^2.

The suite checks epsilon=1/2, 1/10, 1/100, and 1/1000, giving exact losses 1/2, 1/50, 1/5000, and 1/500000. The needed slack coordinates include algebraic values such as sqrt(1/2); they are not claimed to be rational. All residuals and the objective contain these coordinates only in even powers, so the evaluator uses their rational squares exactly. It rejects odd powers rather than approximating radicals. This tests the full displayed slot residuals using Fraction arithmetic, not just a separate hand-written loss formula.

These are different infeasible inputs with losses approaching zero. They do not exhibit unattained infimum zero for any single fixed input.

## Limits

The tests are exact finite examples and symbolic identities, not a general real-algebraic solver. They do not prove convergence of gradient descent, provide a general infeasibility certificate search, or establish feasibility from approximate floating-point residuals. Rational factor data need not have rational square-root slacks; the rational-lift helper deliberately rejects such a lift instead of silently approximating it. The separate even-coordinate evaluator handles the small-residual family by using exact rational squares of algebraic slack coordinates. The native generator checks through length four test this explicit phase construction; they are not presented as a general finite-horizon equivalence theorem.
