# End to end discovery of a calibrated executable report

29 October 2026. This finite implementation connects source-program selection, data eligibility, simultaneous uncertainty, exact risk optimization and a checkable certificate in one run. It is a small implementation test of the general theorem, not a hard physical-discovery benchmark or a new statistical method.

## Plain language abstract

The solver starts with two separate stopping-risk signals and does not receive the correct joint report as its chosen representation. It searches every Boolean report of the two signals, uses confidence bounds valid simultaneously for the entire search, and checks each candidate against every compatible joint probability law. It selects the coincidence report, or its complement, as the only successful one-bit representation. It also synthesizes a distributed implementation and checks how much communication that implementation needs. If the data were never aligned across the two signals, the same program is merely a proposed future measurement; no joint confidence bound is invented.

## 1 Inputs and what is not assumed

Let X and Y be binary delayed-reaction and weak-braking flags. The stopping-envelope note supplies the separate physical premise under which h(X,Y)=X AND Y upper-bounds the modeled stopping violation. This test does not establish that premise. The illustrative surrogate risk budget is alpha=1/50, and the confidence failure budget is delta=1/20. For an actual physical-risk conclusion any separate transfer error must also fit the budget.

A constructed validation histogram has 300 independent same-context episodes: 240 with (X,Y)=(0,0), 30 with (0,1), 30 with (1,0), and none with (1,1). No physical robot data were collected. Independence is between whole validation episodes, not between X and Y. A deployment-law mismatch, outcome-dependent censoring, altered controller or safety-relevant logging overhead is outside this fixture unless separately modeled.

The candidate representation language is every Boolean table f:{0,1}²→{0,1}, exactly sixteen tables. This is a finite budget of observable programs, not a finite list of latent environments. The unknown whole law ranges over every probability distribution on the four scenarios consistent with its evidence. No independence model is imposed.

The existing coarse representation retains every event function depending only on X or only on Y. Including constants, there are six distinct such functions. The proposed new report may retain an arbitrary one-bit Boolean function, and its two output-event probabilities are the rows for f and 1−f. These complementary event functions are already members of the same sixteen-function confidence family; they do not create thirty-two different events.

## 2 One confidence construction for every searched statistic

For each Boolean function f, compute its count k_f in the aligned validation archive. Use a one-sided exact binomial upper interval at failure probability delta/16=1/320. The implementation rounds the endpoint UPWARD to the grid with denominator 2000.

For k<300, choose the smallest j such that

    sum_(i=0)^k binomial(300,i) j^i (2000−j)^(300−i)
       <= 2000^300 / 320.

Then U(k)=j/2000. For k=300 set U(k)=1. The checker compares integers after multiplying by 320; it does not trust a floating-point tail calculation. The only counts arising in this fixture and their upper endpoints are:

    count 0:   39/2000
    count 30:  313/2000
    count 60:  27/100
    count 240: 1719/2000
    count 270: 471/500
    count 300: 1.

Why this procedure is valid: for any true event probability p, U(k)<p implies that the binomial lower tail at k under p is at most 1/320. Since the event U(K)<p is a lower tail in K, its probability is at most 1/320. Upward rounding only enlarges U. A union bound over all sixteen functions gives one event of probability at least 19/20 on which every interval is valid. Dependence between their counts is irrelevant to that union bound. Selection after examining these same data is covered because all candidate event functions were included in advance.

In particular, the zero-count bound is 39/2000=0.0195<0.02. Its finite rational check is

    (1961/2000)^300 < 1/320.

There is no unproved switch between different interval formulas at different observed counts. The same binomial inversion procedure is used throughout.

## 3 Exact robust search and informative failure

For a selected event family S, form the polytope

    p>=0, sum p=1, f·p<=U(k_f) for every f in S.

The risk is p(1,1). The script solves each four-atom linear program exactly by enumerating its vertices: normalization plus three active inequalities determine a candidate vertex, followed by rational feasibility checks against all inequalities. The feasible polytope is bounded and nonempty; a linear maximum occurs at one of these checked vertices.

With only the six local event functions, the maximum risk is 313/2000. One exact optimizing law is

    p=(1687/2000, 0, 0, 313/2000).

This is a concrete adverse explanation allowed by the selected representation. A simpler nonoptimal adverse law (9/10,0,0,1/10) is also compatible with those confidence constraints. The observed empirical marginals are not treated as exact population probabilities.

The solver evaluates all sixteen candidate one-bit report tables, adding both output-event rows. Exactly two succeed:

    f=(0,0,0,1), the AND report;
    f=(1,1,1,0), its complement.

Both induce the same two-cell partition of the four scenarios. Their exact robust maximum is 39/2000, below alpha. The initial adverse optimizer violates the newly retained AND row, so this is also a concrete instance of countermodel-guided row refinement.

The dual certificate is particularly short: the hazard indicator is exactly the calibrated output event of the selected report. Hence E[h]<=39/2000 for every law in the resulting confidence set. The pointwise domination is equality on all four scenarios, checked directly. The successful bound does not select a favorable hidden law and reject other compatible laws.

No added report fails, while one nonconstant bit succeeds, so one added report bit is minimal within this declared language and starting representation. In fact the AND report alone, with its calibrated event bound, suffices; the local counters can be omitted from this particular risk certificate. This is not a universal statement about minimal sensing, total storage or other controller tasks. A streaming event counter over 300 records needs nine bits, plus sample-count and alignment metadata where required; archived raw records are a separate storage cost. The one-bit claim concerns the per-episode report alphabet, not the entire observer or dataset memory.

## 4 Executability has a separate synthesis check

For future distributed acquisition, owner A reads X, owner B reads Y, and the required report is delivered at B. The admitted schedule has a sender encoding phase followed by message delivery and B's decoding phase. The sender may not inspect Y. A candidate program is an encoder e:{0,1}→M and decoder d:M×{0,1}→{0,1}, satisfying

    d(e(X),Y)=f(X,Y)

on all four scenarios.

The script enumerates every encoder and decoder table for message alphabets of sizes one and two. For each of the sixteen report functions it checks exact realizability. With one message symbol, precisely the Y-only functions are realizable. With two symbols, every Boolean report is realizable by sending X. For AND or NAND, the two sender values have different response rows as Y varies, so one symbol cannot suffice. One actual A-to-B bit is necessary and sufficient under this one-way schedule.

This is a runnable program-level witness, not an arbitrary joint mathematical statistic. It is also not hardware attestation. Sensor calibration, read permissions, delivery time and noninterference with the stopping maneuver remain explicit physical capability assumptions. A two-phase protocol, another receiver location or existing centralized access changes the implementation problem and must be charged separately.

## 5 Aligned archives and unaligned marginals are not interchangeable

Three cases are kept distinct.

1. If the aligned raw archive is already available at the analysis collector, every Boolean replay function can be computed there without new acquisition communication. The unknown retained report is selected from those replayable functions. The prospective one-bit communication lower bound does NOT obstruct this already possible offline analysis.
2. If the chosen statistic is to be acquired in future by the distributed A/B hardware, the encoder/decoder synthesis establishes its declared runtime message cost. That is a prospective measurement implementation, not an additional condition for a confidence bound already obtained from an aligned archive.
3. If only unaligned marginal archives exist, the existing-data eligibility check excludes joint functions. The robust risk remains 313/2000 in the corresponding constructed marginal-confidence fixture. The successful AND program is then a proposal for new aligned observations; it contributes no new interval until those observations are acquired.

The last case also has an exact population-information obstruction, independently of finite interval width. The laws

    p_safe=(4/5,1/10,1/10,0),
    p_adverse=(9/10,0,0,1/10)

have identical complete X and Y marginals but hazard risks zero and 1/10. Arbitrarily many additional separate marginal samples cannot distinguish them. A joint task statistic can distinguish them, but the existence of its code does not tell us which law is actual.

## 6 Verification and scope

Run `python3 tests/check_end_to_end_discovery.py`. It constructs all sixteen candidate reports, computes all confidence endpoints by exact integer tails, solves the resulting rational ambiguity programs, checks the selected dual and adverse witnesses, and performs thirty-two message-alphabet synthesis searches, testing 1,088 encoder/decoder table pairs in total (68 per report). It also checks that unaligned data do not acquire a new joint row.

This fixture closes an implementation chain that separate LP and program tests alone would not establish. The general theorem remains conditional on its experiment, hazard and capability contracts. The search language and data are small and explicit; the example does not claim scalable optimal sensor design or a novel linear-programming mechanism. Its two equivalent successful encodings also prevent a fictitious unique canonical representation claim.
