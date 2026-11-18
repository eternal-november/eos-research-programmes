# Retained-state tracking and actual output envelopes

Status: derived scalar integrating-factor bound and exact conditional constructor with independent bounded review, extracted from the frozen baseline's PRIMARY-ASSEMBLY tracking argument. This is elementary existing mathematics, with its proof below; no novelty claim or new device is made. The source law and work account are the RC trackers in RESOURCES at fb85a7606f45e52d0cd48e023ab9776dd526640c. The changed publication and coupling sources consume the same calculation through [tracker_envelope.py](tracker_envelope.py). A powered interval, actual held command, source error, physical gain and output weights remain realization obligations. The result is not a ready-within-H certificate or the global world invariant.

## Local law and retained distinctions

On an interval starting at s, let y be absolutely continuous and satisfy y'=gamma(t)*(c(t)-y(t)) almost everywhere. Assume gamma is measurable and locally integrable with gamma>=g>0, and c is measurable in a finite interval[a,b]. Let the admitted initial value lie in[ilo,ihi]. For tracking, let the reference r be absolutely continuous, with |r'|<=L, |c-r|<=delta almost everywhere and r(s) in[rlo,rhi]. Commands may jump; no differentiability of c is needed. The lower gain holds throughout the claimed interval, not only when a software flag is true. In this source hardware quanta are the time unit.

Define E_range=max(0,a-ilo,ihi-b) and E_tracking=max(|ilo-rhi|,|ihi-rlo|). An input E at least both is a common conservative initial residual. The constructor checks these separate requirements before using E. A general absolutely continuous reference alone does not justify E=2; its initial range matters.

With G(t,u)=integral_u^t gamma(v)dv and rho(t,u)=exp(-G(t,u)), the integrating factor gives y(t)=rho(t,s)y(s)+integral_s^t rho(t,u)gamma(u)c(u)du. The integral weights sum to1-rho(t,s). Thus

    a-E_range*exp(-g*(t-s)) <= y(t) <= b+E_range*exp(-g*(t-s)).

Subtracting r and integrating its absolutely continuous derivative gives

    |y(t)-r(t)| <= E_tracking*exp(-g*(t-s)) + delta + L/g.

The delta term uses integral rho*gamma=1-rho<=1; the reference term uses integral rho<=1/g. For integer n>0, exp(-g*T)<=(1+g*T/n)^(-n), by1+z<=exp(z) for z>=0. All constructor values are exact rationals; the written inequality, not a floating-point exponential, licenses their interpretation. The same bound holds after time T while the premises continue. The widened range[a-E*decay,b+E*decay] is itself forward invariant under c in[a,b].

The representation retains y and its initial residual. It forgets the detailed gain/command history only inside these one-sided bounds; it does not forget stored work, faults or physical output identity. A zero-gain interval, a different command range, a reset of y, reference jumps, a hidden output branch or a new weighting law reopens the corresponding premise. Equal current DAC values need not mean equal current outputs.

## Concrete changed-source use

For command and reference ranges[.3,.9], initial y in[-1,1], g=.01, T=10000 and n=10, E_range<=1.3 and E_tracking<=1.9, so E=2 is valid. Put epsilon=2/11^10. Actual y then lies in[.3-epsilon,.9+epsilon]. Exact membership in[.3,.9] does not follow from a finite settling interval. The elementary local countercase c=.3,y(s)=-1 gives y(t)=.3-1.3*exp(-G(t,s))<.3 at every finite time with finite G. This refutes that component implication; it is not by itself an admitted full-controller trajectory or a counterexample to the frozen baseline theorem. The baseline bytes remain unchanged.

For the new rank-one X/X+Y rows the decoder is x=r0 and y=r1-r0. Its row-error factors are1 and2. There is no division-by-two rounding in that decoder. The retained .0005 in the publication budget is conservative reserve; the actual final WORLD integer floor contributes less than.01. At held-DAC reference age A, beta=.005+4*10^-7*A bounds each good row, conditional on the actual publication/receipt and support suppliers. The conservative command error4*(beta+.0005)+.01 covers both coordinates. The existing A=29704195/1048576 is a bound on the age supporting the held command, not on RC memory. Ordinary command-force retirement is a different causal path. The RC state has no finite last-effect time.

The DAC age needs a continuing-stream premise, not only a delay after a command becomes stable. For the actual ordinary sampler, require nominal snapshot gaps at most S=1/64 and delivery/decoding of every snapshot within D=1, without suppressing a newer snapshot. At time t, a snapshot taken after t-D-S has already arrived by t. Any later arrival that overwrites it was taken within D of that arrival, so reordering still leaves the held snapshot no older than2D+S. This bound applies after the initialized delivery prefix; absent, dropped or unpowered samplers do not satisfy it. With mailbox update gap at most2F_max, sample-to-mailbox work at most F_max and raw row history13, the full held-command age is at most13+3F_max+2D+S=19234819/1048576. The retained published age exceeds this by639/64. Stable-command delay3 alone does not prove the same statement for a continually changing stream. These are explicit conditional premises from the ordinary sampler/flight interface; the enlarged endpoint, energy and reset graph still owes their actual realization.

Let r=clip(2*x-.4,.3,.9). The raw coupled-plant coordinate slew below2 per plant-time unit and tau_plant=10^-7 give L<=4*10^-7 per hardware quantum. The lag is at most1/25000. Adding this lag and epsilon to the command error gives a strict bound below.04. Hence nominal actual output is above.84 on the upper collar x in[.64,.65] and below.36 on the lower collar x in[.35,.36], after the actual10000q interval with these command premises. This is a local conditional collar supplier. A first-exit/shorter-prefix proof must establish the premise intervals and preserve actual resource/work and input support; the calculation does not infer them from the desired invariant.

Nonnegative output weights summing to1 preserve a common range and tracking-error bound when every nonzero-weight nominal tracker satisfies it relative to the same reference. Unformed trackers need zero weight or a separate bad-output charge. Weighting does not reset a tracker, erase its energy, or supply its gain. An initial selected tracker at.6 has zero range defect; a later selected tracker initially elsewhere in[-1,1] needs the finite residual unless a stronger actual entry relation is proved.

With m actual hosts, at most six lost ordinary hosts and complete anomalous export weight W=M+6, the revised service floor is(.3-epsilon)*(1-6/m)-W/m. The formed-output slew uses.9+epsilon. The upper/lower collar floors.84/.36 remain justified by the strict tracking-error bound. Regional coupling checks all these inequalities at its fixed actual m. This preserves the source's physical service definition; incoming coupling is not relabelled effector service.

## Checking and remaining assembly

The constructor rejects nonexact values, booleans as counts, invalid intervals, nonpositive gain and an insufficient initial residual. Its exact affine cases retain the finite-range and finite-memory counterexamples. The integrating-factor derivation supplies the continuum result; finite cases are executable evidence, not a proof of arbitrary histories. Publication timing and regional coupling bind the constructor and this statement in their result records. Full source admission, uninterrupted energized command intervals, mutable-controller formation, actual weights, complete work/heat accounting and all-history recurrence remain parent obligations.
