# Discovery of an exterior-robust task quotient from partial readouts

## Plain-language result
A sensor patch may contain both a useful local mechanism and variables driven by an unobserved surrounding system. We give a procedure that learns which distinctions inside the patch must be retained to predict a designated task readout, discovers the necessary input history, and either constructs an autonomous local model or returns a finite obstruction. The surrounding system need not be identified, finite-state, or fully instrumented. The price is an explicit experimental promise: a randomized probe must change every admitted hidden bypass in a uniformly separating way. Ordinary observation alone cannot certify this promise.

The result is a local predictive and causal factorization. It is not yet a physically sealed two-way replacement theorem: the unresolved remainder can still read private local state. An additional outward-interface theorem would be needed to forbid that access.

## 1. Universe and access
Fix one candidate instrumented patch with finite latent alphabet X, |X|=d. Its alphabet and sensor calibration are initially unknown. There are three conditionally independent full-column-rank noisy views of X, with positive state probabilities and the usual identifiable finite-mixture conditions. The same calibrated channels are used in aligned bounded histories; sensor noise is conditionally independent across sampled times and channels given the latent path. This permits tensor-product left-inverse recovery of bounded latent-history laws. Correlated sensor noise would require a different observation theorem. An existing local calibration theorem, or exact identified observation laws, supplies the joint laws of X_t, X_{t+1}, and bounded candidate input histories. Nothing outside these instrumented patches need have a sensor.

There is a bank of m actually accessible input channels, each of bounded alphabet, and a maximum history length L. A candidate input context A selects at most k channel-lag slots. Its value is denoted w_A. Recorded actions may be included among these slots. The learner is not given the correct subset. For the arbitrary-input-policy conclusion, require pair-union coverage: for every pair of candidate contexts A,B of size <=k, every Cartesian value of (X_t,w_{A union B}) has positive sampling probability, quantitatively at least rho when rates are claimed. This covers up to 2k slots, not merely each context separately. It prevents selecting a spuriously sufficient substitute input because two ports happen to agree in training. If physical constraints forbid this support, conclusions are instead restricted to input policies preserving the covered support, or a separately specified admissible-support version must be proved.

Write H_t for the full pre-probe history, including X_t and all current input symbols. H_t may contain an arbitrarily large or infinite-memory unobserved exterior. After this history is fixed, a binary randomized probe R_t is drawn independently of H_t. A hidden mode Z_t is then drawn with

  P(Z_t=1 | H_t,R_t=r) = p_r(H_t),
  p_1(H_t)-p_0(H_t) >= delta > 0.

For some UNKNOWN context A_* of size <=k, there is a fixed response kernel F such that

  Law(X_{t+1} | H_t,R_t,Z_t=z) = F(. | X_t,w_{A_*},z).

The probe has no direct local effect except through Z. The exterior can govern inputs, mode probabilities, and its own subsequent evolution arbitrarily, including feedback from the local system. F need not be linear, product-form, deterministic, or injective. This is a bound on how hidden influences act on this patch, not on the size of the exterior. It is a substantive causal model-class promise, not something established merely by fitting observed moments. Multiple hidden modes can instead use a conditional full-rank expectation operator; see the separate exterior theorem.

A task signature h:X -> T is specified or learned from a designated task-readout conditional law. For the latter, the task channel must be conditionally memoryless/independent given the latent path with its declared timing, and the realization retains that conditional channel; equality of isolated one-time emission marginals is not enough to preserve task transcripts with hidden correlated noise. It need not identify X. A permitted local quotient pi must preserve h: h factors through pi. If h is injective, no compression is possible; if h is constant, triviality must be prevented by another explicit task requirement. Sensor calibration does not give the runtime controller noiseless access to X.

## 2. Finite probe test detects hidden response dependence
For a partition Pi of X, let F_Pi(B|x,w,z)=sum_{x' in B}F(x'|x,w,z). For every candidate context A, x, supported w_A and block B, compare

  P(X_{t+1} in B | X_t=x,w_A,R_t=0)
  P(X_{t+1} in B | X_t=x,w_A,R_t=1).

**Lemma 1.** All these equalities hold if and only if F_Pi(.|x,w,0)=F_Pi(.|x,w,1) on the admitted response support.

**Proof.** If the two F_Pi rows coincide, the next-block law is a function of pre-probe history alone. R is independent of that history, so averaging under any pre-probe context preserves equality. Conversely take A=A_*. At fixed x,w the observed difference for block B is

  E[p_1(H_t)-p_0(H_t) | X_t=x,w_{A_*}=w]
       * (F_Pi(B|x,w,1)-F_Pi(B|x,w,0)).

Randomization makes the conditioning distribution of H_t the same in both regimes. The first factor is at least delta. Every nonzero response difference is therefore detected. QED.

This test does NOT discover the observed boundary by itself: omitting an input unaffected by R can leave regime invariance intact. Boundary discovery is the next, distinct step.

## 3. Recover the observed response without exterior identification
If Pi passes Lemma 1, write K_Pi for its mode-independent response. Search contexts A of size <=k minimizing

  H(Pi(X_{t+1}) | X_t,w_A,R_t).

The minimum equals H(Pi(X_{t+1})|H_t,R_t), because A_* attains it. For a minimizing A, the conditional KL identity

  H(Y|X,w_A,R)-H(Y|H,R)
    = E[ KL(Law(Y|H,R) || Law(Y|X,w_A,R)) ]

implies equality of the kernels almost surely. Thus an entropy-minimizing context recovers K_Pi as a finite row table, with no model of the input process or exterior. R is redundant after the successful probe test. Pair-union coverage of A union A_* upgrades this almost-sure equality to equality for every joint assignment of their inputs. Hence the recovered sparse table agrees pointwise with the true sparse response under any input policy in the declared Cartesian universe. Coverage of A and A_* separately would not suffice: ports U=V during training could falsely justify replacing a true V dependence by U.

For finite data use a confidence-tolerance band around the minimum BEFORE choosing a smallest context. Exact empirical argmin followed by cardinality minimization is not valid.

## 4. Constructive task-preserving subsystem discovery
Start with Pi_0, the partition into equal task signatures h(x). Iterate:

1. Apply Lemma 1 to Pi_j. If it fails, return the witnessed x, input context, block, and regime contrast.
2. Recover K_{Pi_j} by Section 3.
3. Split each old block according to the complete response signature

       x -> ( K_{Pi_j}(B|x,w) : B in Pi_j, all admitted w ).

   Call the resulting partition Pi_{j+1}.
4. Stop when no split occurs.

At most d-|Pi_0| strict refinement rounds occur. A row table may use a different recovered sparse context in each round; their union has at most kd slots, so comparison of signatures never requires an exterior-state table. With fixed d,k,L and input alphabet bound, enumerating candidate contexts is polynomial in m; dependence on these structural widths is exponential and calibration/margin constants can be poor.

**Theorem 2.** If the algorithm terminates successfully, its partition Pi_* is the coarsest task-preserving quotient whose next-state kernel (i) is independent of the hidden mode and (ii) depends on the old patch state only through the quotient and the admitted input history. If a probe failure occurs, no such quotient exists within this patch-state universe.

**Proof.** A successful fixed point has the asserted properties by Lemma 1 and equality of row signatures within each block. For maximality, let Q be any valid task-preserving partition. Initially Q refines Pi_0. Inductively, if Q refines Pi_j, each Pi_j next-block is a union of Q blocks. Its response is therefore independent of the hidden mode; a probe failure for Pi_j contradicts validity of Q. Also states in one Q block have equal probabilities for every next Q block at every w, hence equal probabilities for every next Pi_j block. They cannot be separated by the splitting step. Therefore Q refines Pi_{j+1}. At termination Q refines Pi_*. QED.

The obstruction proves nonexistence only among deterministic quotients of this calibrated patch state, preserving this task, under this input/history universe and causal promise. It does not exclude larger patch states, longer memory, new instruments, or an explicitly different task.

## 5. Discover a recursively implementable input boundary
Let U be the selected union of input channels and let W be its length-L raw history register. At the fixed point, local response is K(s'|s,w,a), with action separated if desired. Begin with equivalence of histories having equal K rows for every s,a. Refine by demanding that equivalent w have equivalent shifted histories shift(w,u) for every admitted new input u. Finite partition refinement terminates at the coarsest deterministic causal history quotient beta preserving response rows.

Then

  s_{t+1} ~ K(.|s_t,b_t,a_t),
  b_{t+1} = update(b_t,u_{t+1}),

with b=beta(w). Search input-channel subsets and retain those whose response rows ignore omitted channels; this is checked by full kernel row comparisons, not probe invariance. The selected channel subset need not be unique. This gives a finite implementable boundary transducer, not free access to Z or arbitrary noncausal preprocessing. Memory and input wires are charged explicitly. In a latent-port variant the same algebra discovers a GENERATIVE interface register and its noisy observation channel; it is not an exactly maintainable register for an external controller. Population-law calibration does not decode the latent port on each run. The directly implementable transducer claim applies only when the input symbols themselves are physically accessible; the noisy stress family must be labeled as the generative variant. Coarsest state quotient and coarsest boundary for that state quotient are not claimed to optimize every joint state/interface cost tradeoff.

## 6. Positive local realization and exact whole-law witness
K is stochastic and nonnegative, hence a constructive local mechanism. The remainder of the actual whole need not be learned. At each history and chosen port value, its whole next-step law P has marginal K on s'=pi_*(X'). Factor it by ordinary conditional disintegration:

  P(s', remainder' | full history) = K(s'|s,b,a)
       * P(remainder'|full history,s').

For finite or standard Borel remainder spaces use regular conditional laws. Zero-probability branches may be assigned arbitrary normalized remainder kernels. In particular the retained patch remainder lies in the dependent fiber pi_*^{-1}(s'); unequal fibers cause no difficulty. This generates exactly the original whole law and all correlations, rather than replacing it by independently sampled pieces.

Every exterior satisfying the same response promise and timing can change its size, memory, input policy and mode law without changing K. The randomized probe is needed for identification, not for deployment: after pointwise mode independence is established, the same K applies with the probe removed and under arbitrary admitted mode policies. Conditional invariance is pointwise, so adaptive feedback through the pre-probe inputs is allowed. Initial local distributions must be retained or separately bounded. This is equality of OPEN response kernels, not equality of unconditional local trajectory laws across different exterior input policies. Any learned-versus-true trace error comparison must couple the same causal input/exterior policy or impose the same input sequence.

An explicit generative communication contract assigns the residual fiber and exterior history to the remainder, exposes the initial quotient state, and transmits the full new quotient value s' each step. The remainder then has old (s,fiber), hence old X, and the new s' required by the conditional kernel. This charges a full quotient-state message; it does not assert that the physical hardware implements such a wire. A smaller task-output-only message needs its own sufficiency proof.

**Scope warning.** The remainder kernel may depend on full old X and on s'. This witness does not establish a physically restricted outward interface, independent component noise, or arbitrary implementation replacement. It establishes an inward-autonomous task quotient and an exact dependent whole-law realization. A bidirectional interface restriction requires additional outward sufficiency evidence.

## 7. Compatibility is a joint test
Two individually robust quotients need not have a robust join. Let U be a fresh fair bit, and let D be a Bernoulli bit with parameter depending on Z. Set two next-state coordinates to U and U XOR D. Each coordinate is fair independently of Z; the joint disagreement probability depends on Z. Each separate quotient passes, while their joint partition fails Lemma 1. All transition probabilities can be strictly positive. Thus retain joint tests when combining discoveries from several task channels or patches. Separate marginal certificates do not imply coexistence as one exterior-independent module.

## 8. Statistical and resource qualifications
A conditional finite-data stability theorem with explicit error transfers and sampling bound is given in `Finite_Data_Stability.md`; it is not a finite-sample implementation. It additionally needs: identifiable and well-conditioned calibration; context coverage; independent blocks or quantitative mixing/concentration; lower bounds on nonzero effect contrasts, row-separation and context-entropy gaps; and the probe gap delta. If a hidden response block contrast is at least gamma, its observed contrast is at least delta*gamma. Uniform probability error smaller than delta*gamma/4 separates equality from such alternatives. Similar row-margin bounds stabilize partition splits. Approximate models require explicit approximate closure error rather than silently rounding exact equalities.

The algorithm is local in hidden-state size: it never enumerates the exterior. It is polynomial in the number of instrumented candidate input channels for fixed patch size, sparse-parent width, history length and alphabet sizes. It is NOT a general polynomial algorithm for unrestricted hidden architecture discovery. The environmental causal promise and experiment adequacy are not certified by the same readouts. Runtime inference of a hidden quotient state, physical hazard interpretation, and infinite-horizon control guarantees are separate obligations.

## 9. Relationship to existing mechanisms
Three-view latent identification, randomized invariance tests, controlled lumpability/partition refinement, causal history minimization and disintegration are standard ingredients. The integrated result removes full exterior observation and full observed-patch Markov closure, discovers the task-preserving quotient and its recursively usable incoming boundary, and provides a finite failure certificate within an explicit incomplete-observation universe. Influence-based abstraction and local-module identification are close baselines; novelty must be assessed against their supplied local factor/graph/history assumptions, not inferred from this terminology.

## 10. Reproducible checks
`check_refinement.py` checks the exact response-kernel refinement algorithm on the nonlinear contaminated eight-state example. It starts from the two task blocks for a and discovers four blocks for (a,b). Exhaustive enumeration of all 225 task-preserving partitions confirms that this is the only valid partition in that fixture. It separately checks an unequal-fiber quotient and the marginal-versus-joint hidden-correlation obstruction. These are known-kernel algebra checks, not finite-data sensor inference. The independent stress script exercises noisy observation-law recovery.
