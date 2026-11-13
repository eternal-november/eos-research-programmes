# Finite observable behavior certificates: corrected operational bridge

Status: proved finite-basis core and explicit remaining decomposition problem. This corrects any reading of the separator-saturation note as requiring independence from a component's OWN hidden randomness. A hidden coin may generate a perfectly valid Bernoulli component. Only unwanted dependence on a declared external context is an isolation defect.

## 1. Operational semantics, not latent ontology

Fix finite command and readout alphabets A and O. An environment has a controlled readout law f(w), where w is a finite word of command/readout pairs z=(a,o). The commands in w are fixed externally, and f(w) is the probability of the displayed readouts under that command sequence. It is nonnegative, f(empty)=1, and sum_o f(w(a,o))=f(w) for EVERY prefix w and EVERY command a. This is input-total normalization. An illegal or blocked command must therefore produce an explicit recorded/semantic illegal-or-blocked outcome; it cannot silently remove probability mass. This is an operational/history semantics. Different hidden state spaces, private coins and hidden physical refinements may realize the SAME f.

The raw input remains logged readouts, with commands only if actually recorded. Estimating the controlled law from logs requires a justified exogeneity/causal-identification assumption and coverage. Logged action variation alone does not suffice. With no command interpretation, the theorem applies only to the passive readout process.

A decomposition is a typed stochastic-port assembly D whose external controlled law equals f (or approximates it within a declared risk budget). It need not be a literal partition or deterministic quotient of every hidden realization's state. Analysis-only ports do not become sensors or actuators available to the controller.

If all compatible hidden realizations have the same controlled law, D is an operational decomposition for all of them. This does NOT assert that every hidden realization is probabilistically bisimilar to D or admits a physical statewise quotient. Equality under the permitted controller contexts is the claim.

## 2. Exact finite-basis theorem

For finite words p,s define the Hankel matrix H_f(p,s)=f(ps). Fix an independently stated universe-wide observable-rank bound r. This bounds a linear predictive representation, not a known decomposition. Let P,S be proposed sets of r prefix/suffix words such that

 B_f = [f(ps)]_(p in P,s in S)

is invertible. For each command/readout symbol z define B_f,z=[f(p z s)]. Also define the row u_f=[f(s)] and column v_f=[f(p)].

The following finite table determines f throughout that rank-bounded universe:

 B_f, all B_f,z, u_f, v_f.

Precisely, any other valid controlled law g with rank H_g<=r and the SAME displayed finite table satisfies g(w)=f(w) for every word w. Hence it agrees under every adaptive controller using the permitted readout/action ports.

Proof. The r rows indexed by P span the entire row space because B_f has rank r and the full Hankel rank is at most r. Write

 alpha_f=u_f B_f^(-1), M_f,z=B_f,z B_f^(-1), beta_f=v_f.

For an arbitrary prefix h, its row-coordinate vector is

 c_h=[f(hs)]_(s in S) B_f^(-1).

Row-space spanning gives c_(hz)=c_h M_f,z and f(h)=c_h beta_f. Consequently f(z1...zt)=alpha_f M_f,z1 ... M_f,zt beta_f. The same finite table gives the same representation for g. Adaptive control follows by summing word probabilities against the SAME history-dependent action probabilities. QED.

This is standard finite Hankel/weighted-automaton realization. It is a sound foundation, not the proposed new contribution.

## 3. Uniform finite-horizon perturbation theorem

Let f,g both be valid controlled laws of Hankel rank at most r. Use the same P,S. Assume the smallest singular values of both B_f and B_g are at least sigma>0, and every entry in their finite tables differs by at most epsilon. Put kappa=1/sigma and let m be the number of possible readout symbols per command (pad with zero-probability outcomes when needed).

For any SAME adaptive controller and any event E of its length-H closed-loop transcript,

 |Pr_f(E)-Pr_g(E)|
 <= min(1, [2 r kappa + r^2 kappa^2
             + H m (r^2 kappa^2 + r^3 kappa^3)] epsilon).

Therefore the same bound holds for transcript total variation. It permits stochastic components with private/internal noise; it is not a demand that their responses be independent of that noise.

Proof details. In spectral norm, ||B_f-B_g||<=r epsilon, ||B_f^(-1)-B_g^(-1)||<=r kappa^2 epsilon, and ||B_f,z||,||B_g,z||<=r because their entries are probabilities. Thus

 ||alpha_f-alpha_g|| <= sqrt(r) kappa epsilon + r^(3/2) kappa^2 epsilon,
 ||M_f,z-M_g,z|| <= r kappa epsilon + r^2 kappa^2 epsilon,
 ||beta_f-beta_g|| <= sqrt(r) epsilon.

The key is NOT to multiply single-step matrix norm bounds H times. For every prefix h,

 ||alpha_f M_f,h||
 = ||[f(hs)] B_f^(-1)|| <= sqrt(r) kappa f(h),

because f(hs)<=f(h). For an arbitrary future policy and transcript event, the vector of UNNORMALIZED continuation weights from the r basis prefixes has every entry in [0,1], hence norm <=sqrt(r). More explicitly, for an actual preceding transcript h and a basis prefix p, its entry is sum_s pi(s|h) 1_E(hs) g(ps) <= g(p) <= 1, where pi(s|h) is the product of the causal policy's command-selection probabilities along the continuation s. This holds even if that policy carries externally specified controller memory from a different preceding history. No division by the possibly rare probability g(p) occurs.

Expand the difference of the two closed-loop transcript probabilities by replacing alpha, one M at a time, and beta. At each replacement time, sum the f-prefix weights under the causal policy; they sum to one. Sum over commands using their policy probabilities, and over at most m outputs. Each operator replacement therefore costs at most r kappa m ||M_f,z-M_g,z|| uniformly. The initial and final replacements cost at most sqrt(r)||alpha_f-alpha_g|| and sqrt(r)kappa||beta_f-beta_g||. Substitution yields the displayed bound. QED.

No exponential dependence on H appears in this bound. Alphabet size, rank and conditioning can nevertheless be large and must be charged. Infinite-horizon safety or exact support does not follow from finite-horizon TV control.

## 4. Statistical use and costs

The finite table is estimated from the original readouts, not provided as an environment model. A simultaneous confidence statement for all tested word probabilities yields a confidence family of valid controlled laws satisfying the table bands and a lower singular-value bound. If the true law is in the universe and the statistical event holds, the true law remains in that family. Comparing a positive candidate D to every member gives the above operational guarantee.

The costs include: number of tested words, their lengths, rarity/coverage, action propensity or other identification overhead, estimator error, rank/conditioning, searching for P,S, and selection from the same data. Adaptive candidate search needs appropriate held-out validation or uniform control; an uncorrected fit is not a certificate.

A rank bound cannot be inferred merely because a finite observed block has low rank. A hidden counter can agree on all short tests and have higher rank. The hypothesis universe must supply a defensible rank restriction, or the new theorem must derive a complete local predictive-test closure certificate. Full-rank observed B only saturates a valid prior upper bound.

## 5. Positive typed factorization, the still-hard step

The predictive realization can have negative matrix entries in its chosen coordinates. It is NOT automatically a physical stochastic mechanism or a typed decomposition.

The proposer must discover a genuinely nontrivial typed stochastic-port assembly D with unknown interfaces/couplings and a positive realization witness. To invoke the finite-basis or perturbation theorem, D's law must itself have Hankel rank at most r, or D must carry an exact intertwining certificate into an r-dimensional realization proving that bound. Merely fitting the finite table is insufficient: a higher-rank candidate could agree there and disagree later. One possible certificate uses local intertwining squares mapping the assembly's stochastic operators into the learned predictive representation. If these commute with initial and final/readout maps and compose under the typed operations, induction proves equality of all external word probabilities. The witness can be noninjective, allowing hidden refinements and internal randomness.

This must be done directly on local predictive blocks and shared-interface data when the global Hankel rank/product is exponential. The finite-basis theorem above is a local building block, not permission to construct an exponential global Hankel matrix and declare success. Separately fitted local processes may have invisible joint couplings or incompatible persistent alignments. Their positive joint realization and observational coverage require another theorem.

Selected next hard problem:

  Derive a finite, data-estimable, positive simultaneous-realization criterion
  for crossing local predictive representations in the fixed typed port
  universe, with persistent interface witnesses, such that every compatible
  readout law has a witnessed operational decomposition of the accepted type.

The criterion must permit internal stochastic refinements, preserve permitted causal controller contexts, and account for nonlocal invisible coupling. It must not assume known latent atoms, a global root model, or that the proposed local observation tests already separate every competing realization.

At present the exact finite-basis and error lemmas are proved; that local-to-global positive realization/coverage criterion is open. The existing conditional junction-tree theorem supplies a sufficient gluing operation AFTER its interfaces and independence/coverage conditions have actually been established. It does not establish those conditions from readouts.
