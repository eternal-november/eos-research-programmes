Exact costly calibration case

Main files

calibration_solver.py is the main exact reference calculation.
calibration_results.json records all rational results and the model assumptions.
calibration_check.log records the successful run.

Run with Python 3 and its standard library only:
  python3 calibration_solver.py

Model and information

A fixed hidden phase theta is either zero or one. An agent chooses mode r.
For independent Bernoulli primitive faults U1,U2,U3, report A is invalid when
U1 or U2 occurs. Report B is invalid when U1 or U2 occurs if r=theta, and when
U2 or U3 occurs otherwise. The two reports share an underlying source in
both cases; the unknown fact is which sources they share.

A safe calibration fixture supplies a known target, so the raw invalidity
bits (A,B) are observable there. Calibration uses fresh independent primitive
faults with probability 1/5. Operational production uses fresh independent
primitive faults with probability 1/50. The same theta and source-use rule
apply in both regimes. This structural transport rule and both fault rates
are stipulated, not inferred from the observations. The calibration fixture
has zero physical hazard in this model. It costs one unit of time and one
unit of energy. Production takes three time units: two for report acquisition
and one for execution. For energy bookkeeping only, production is stipulated
to cost two units; that number is a convention, not measured evidence.

Production payloads do not reveal theta or fault bits. A production hazard
occurs if either report is invalid. Bad is production hazard OR missed mission
completion, including abort. There is no concurrency, alternate task, or
cheaper substitute. A policy may adapt all calibration modes and stopping
choices to raw history, and may use private randomness. It has at most k
calibration calls before production: deadline k+3, energy allowance k+2.

All claims are per fixed theta and ex ante over the complete policy. The
balanced prior used in the proof is only a lower-bound device, not an assumed
true distribution over environments. No observation is assigned a fresh
conditional error budget after it is seen.

Likelihoods and operational risks

Aligned raw calibration probabilities (00,11,01,10) are
  (16/25, 9/25, 0, 0).
Split probabilities are
  (64/125, 29/125, 16/125, 16/125).
The two marginal invalidity probabilities agree in both cases. The total
likelihood overlap is s=93/125=.744.

Operational hazard is a=99/2500=.0396 when aligned and
b=7351/125000=.058808 when split. Marginals alone allow joint hazard as large
as 2a=.0792, attained by disjoint invalidity events. Thus a marginal-only
failure to certify is not an impossibility proof for the supplied joint model.

Optimal policy and proof

Choose the first mode by a fair coin. Repeat that same calibration mode until
the first disagreement; then stop calibrating and use the opposite mode for
production. If k calibrations all agree, use the initial mode.

In either fixed world, an aligned initial mode is always correct. A split
initial mode remains wrong only if all k reports agree, probability s^k.
The mode error is therefore e_k=s^k/2 in both worlds. Its risk is
  R_k = a + (b-a)e_k = 99/2500 + (2401/250000)(93/125)^k.

For optimality, take arbitrary nonnegative likelihood weights w0,w1 at an
adaptive history. Either calibration mode has overlap s. For its next raw
outcome y,
  min(w0 P0(y), w1 P1(y)) >= min(w0,w1) min(P0(y),P1(y)).
Summing outcomes lower-bounds remaining overlap by s min(w0,w1). Induction
shows that any strategy using at most k further probes has weighted terminal
classification error at least s^k min(w0,w1). Stopping early cannot beat the
bound, because s<=1. Randomized choices are mixtures and preserve it.
Starting at weights (1/2,1/2), every policy's average error is at least s^k/2;
its worst-world error is at least its average. The displayed policy attains
that value in both worlds. Abort and deliberate missed completion cannot help:
replacing either by a feasible terminal production attempt has hazard at most
b<1, while abort has Bad probability one. This yields the same minimax risk
bound for the declared completion objective.

At threshold .045, zero and one calibration calls are insufficient, with
risks .049204 and .046745376. Two suffice, with risk .044916159744. The two-call
policy uses 1.872 calibration calls on average in each world and leaves theta
ambiguous with probability .776768. On every all-agreement history, both phase
likelihoods remain positive. Thus most successful attempts do not identify the
phase exactly. These are calculated probabilities, not sampled trial counts.

Validation

An exact rational posterior dynamic program considers both calibration modes,
both terminal modes and optional early stopping. It matches the formula for
k=0 through 6. A separate unpruned enumeration checks every deterministic tree
over three information-distinct observations through k=2: 2 + 18 + 11666 =
11686 policy trees. The two discordant orientations have identical likelihood
and costs, so keeping them separate cannot improve the optimum at a decision
node; private randomization is already admitted.

A separate replay computes raw four-outcome calibration laws from all eight
primitive fault assignments and traverses the explicit policy in each fixed
world. Operational hazard is likewise computed directly from primitive faults.
It checks risk, normalization, expected calibration count, remaining ambiguity
and worst-case call budget. All arithmetic uses fractions; no solver tolerance,
Monte Carlo confidence or deadline-timeout result enters the claims.

What fails without the transport premise

Allow two production links for each calibration phase: stable theta_production
=theta_calibration, or reversed theta_production=1-theta_calibration. They have
identical calibration transcripts under every allowed calibration policy.
For any eventual production-mode distribution, their average hazard is
(a+b)/2=.049204. Therefore no amount of this calibration can certify risk below
.049204 uniformly over both links. A blind fair mode choice attains the bound.
The two-call policy optimized for the stable link instead has .053491840256
risk under the reversed link. This does not show a failure of POMDP planning:
it exposes an unobservable structural premise in the restricted experiment
regime. Different admissible experiments could change that conclusion.

Scope

The computation solves a supplied finite model with unknown persistent phase.
It does not discover arbitrary decomposition structure, estimate fault rates,
validate the safe fixture, or establish the calibration-operation link. It is
a worked application of ordinary finite partially observed planning and an
exact overlap argument, not a claimed new general composition theorem.

Archive contents and reproduction

Run python3 calibration_solver.py from this directory. The program rewrites
calibration_results.json and prints the checks recorded in calibration_check.log.
The TXT report summarizes the findings. audit.txt records independent
mathematical and code review. MANIFEST.sha256 lists the SHA-256 of every
other archive file; verify with sha256sum -c MANIFEST.sha256.

Editorial packaging notes: the README omits references to an excluded earlier
fixture and clarifies a statement about phase uncertainty. The audit omits one
internal coordination sentence. Solver, results and run log are unchanged.
