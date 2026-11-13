# Candidate main theorem: paired-response discovery without a complete probe

STATUS: PROPOSED ROUTE; not a completed replacement theorem. This is a different experimental access contract, not something implied by ordinary randomized interventions or three noisy sensors.

## Plain-language statement
One need not identify every hidden exterior influence to find which local distinctions matter. If two local trials can experience the same hidden exterior condition while their own fresh randomness is independent, their joint outcomes tell us whether two local situations have the same response to that hidden condition. Repeating this comparison lets us discover a task-preserving local state and its observed input boundary. The hidden condition is retained as a shared, unresolved input—not silently removed. Some higher-order and temporal behavior remains undetermined even when all these comparisons are known.

The price is paired-response access. Setting up two such trials may be difficult physically. This does not solve discovery from arbitrary passive readouts. Its improvement over a complete-probe assumption is precise: no intervention must perturb, label, calibrate, or distinguish every hidden influence. A probe with only one regime is allowed.

## 1. Explicit universe and experimental access
Let X be a finite local patch alphabet and U a finite admissible input-history alphabet. A designated nonconstant task signature h:X->T is given or identified from a properly timed task-readout channel. Neither the sought partition of X nor the useful quotient of U is supplied.

There is an arbitrary standard-Borel hidden effect space Z and a probability measure mu. At each challenge context c=(x,u), the patch response is a stochastic row f_c(z) in Delta(X). Its coordinates are f_{c,y}(z). Dependence on x,u,z can be nonlinear and nonproduct.

A paired challenge at c,d uses the SAME draw z~mu in both trials, with conditionally independent next outcomes Y_c,Y_d given z. Thus

  m_{c,y} = integral f_{c,y} dmu,
  G_{c,y;d,y'} = integral f_{c,y} f_{d,y'} dmu.

Both c=d and c!=d challenges are needed. The input/local-state challenges must leave the exterior draw and other trial's mechanism unchanged; the two local innovation sources must really be conditionally independent. These are exclusion, alignment, and replication assumptions. Independent one-shot trials with independently redrawn z do NOT give G. Three noisy views of the SAME next state identify that state's law, not the square of its response probability, and cannot substitute for response replicas.

X itself and its sensor channel may be latent and learned by an independent three-view calibration theorem, provided initialization/conditioning of challenge contexts and calibrated cross-trial readouts are justified. Calibration is not noiseless runtime decoding. A first theorem may take exact deconvolved m,G as its observation-law input, and must credit that access separately.

The experiment need not identify mu, Z, or the full response functions. Its coverage is on local challenge pairs, not on hidden modes. Deployment conclusions concern hidden response conditions in the mu-essential support, or require an explicit absolute-continuity/support-transfer promise. No conclusion about unvisited effects follows from finite data or null integral alone.

## 2. Observable equality of hidden response functions
For any finite coefficient vector a indexed by (c,y), put f_a=sum a_{c,y} f_{c,y}. Then

  ||f_a||^2_{L2(mu)} = a^T G a.

Consequently f_a=0 mu-a.s. iff a^T G a=0. In particular, for next-state block B and contexts c,d,

  D_B(c,d) = sum_{y,y' in B} (G_{c,y;c,y'}+G_{d,y;d,y'}-2G_{c,y;d,y'})
           = integral (f_c(B)-f_d(B))^2 dmu.

Thus D_B=0 certifies equality of the entire hidden-condition response function for that block, not merely its observed average. No inverse of a regime-by-hidden-mode matrix is used. A single experimental regime can suffice.

For finite alphabets there are finitely many queried relations, so their almost-sure equalities hold on one common full-mu-measure set Z0. All subsequent exact realization statements use Z0.

## 3. Discovery theorem
A deterministic partition P of X is conditionally closed if, whenever x~P x', for every u and every block B of P,

  f_(x,u)(B,z)=f_(x',u)(B,z) for mu-almost every z.

This is lumpability CONDITIONAL ON the retained hidden influence. It is not exterior independence. Start P0 as the task partition. Given Pj, split each old block according to equality (in L2(mu)) of all response functions f_(x,u)(B), for u in U and B in Pj. The comparisons are exactly the observable zero tests D_B.

**Theorem 1.** The algorithm terminates after at most |X|-|P0| strict refinements at the unique coarsest conditionally closed partition P* refining the task partition.

**Proof.** Finite refinement terminates. At a fixed point its defining equalities give conditional closure. Let Q be any conditionally closed task-preserving partition. Inductively Q refines Pj. If x~Q x', their response probabilities to each Q block are equal as functions of z. Summing over the Q blocks in any Pj block shows equality of all response signatures used at stage j. Hence Q refines Pj+1. Therefore Q refines P*. QED.

The certificate consists of the partition, all required zero quadratic forms, and a refinement trace showing minimality. This certificate is relative to exact m,G and the paired-response universe; it does not certify that physical experiments obey that universe.

## 4. Discovering observed boundary memory
With P* fixed, define u~0 v iff f_(x,u)(B)=f_(x,v)(B) in L2(mu) for every x and P* block B. All comparisons again use G. If U is a finite shift register with update tau(u,a), repeatedly refine this equivalence until u~v implies tau(u,a)~tau(v,a) for every permitted new input a. The result beta is the coarsest deterministic recursively updatable input summary preserving the hidden-condition response functions.

The local kernel k_z(B|s,b) is well defined on the common full-measure Z0. beta is a runtime-maintainable register only if its input symbols are physically available and initialized; latent/noisy input symbols yield a generative interface, not exact controller access. Enumerating U can be exponential in history length and input count. This theorem by itself does NOT imply sparse-input polynomial complexity.

## 5. Certified autonomy versus retained uncertainty
For any component row k_z(B|s,b), its variance

  integral k_z(B|s,b)^2 dmu - (integral k_z(B|s,b) dmu)^2

is readout-determined. Vanishing for every row and B certifies exterior independence on Z0. Otherwise the discovered component is a mechanism with a genuinely retained hidden input. Declaring it autonomous merely because ordinary regime averages agree is false.

The positive completion family consists of measurable maps f into the product of response simplices and source measures matching m,G, together with separately declared temporal source laws. Positivity and normalization are essential. PSD of G is necessary but not generally sufficient for such a simplex-supported moment realization. At least one realization exists by the universe promise; solving all realizations can be expensive. The discovery algorithm above does not enumerate or solve this moment-realization problem.

Every completion has the SAME discovered conditional quotient, because each zero quadratic form holds almost surely in every representing measure. This is a nontrivial separation between discovering a reusable local quotient and identifying the exterior realization. With a full Gram matrix, every deterministic quotient closure test has the same truth value in every completion under this almost-sure criterion. World-specific closure claims can arise only with partial Gram data, changed deployment support, or additional temporal/structural restrictions; those witnesses must remain attached.

## 6. Joint realization, not independent local resampling
For one fixed completion, a single source realization z is shared by all components that refer to that source occurrence. Their conditional local kernels and the stipulated coupling law form one positive joint law. If independent local innovations are promised, the joint outcome probability is an integral of the PRODUCT of their conditional kernels. One may not multiply their separate integrals.

Second moments fix pair interactions but generally not third or higher interactions. A temporal source law must likewise be shared across all times, with its initialization retained; the same one-time moments are not a certificate of a trajectory law. Arbitrary switching among compatible completions at each time changes the uncertainty semantics and is not licensed.

The quotient maps above commute pointwise with pushforward of the conditional kernels on Z0. Therefore for any FIXED globally coherent source realization, pushing forward a fully coupled execution in either refinement order gives the same joint execution law. This is a concrete witness for refinement compatibility, not proof of a full virtual-equipment construction. Unequal quotient fibers and correlated residuals require conditional disintegration, not an independently sampled Cartesian remainder. Outward/private-state access and communication must be charged separately.

## 7. Missing pair tests and statistical limits
If G is only partially measured, an equality is certified only if it holds for every positive completion of the available joint laws. A measured positive D_B is a direct obstruction. An unmeasured D_B is not zero by default. Asking for that specific paired challenge is a concrete additional-test obligation; whether that challenge is physically realizable remains external.

With entrywise Gram error <=epsilon and |B|=b, direct evaluation of D_B has error <=4b^2 epsilon. Exact equality cannot be decided uniformly from finite samples without a nonzero-gap promise. Under a known separation gap gamma between zero and positive tested squared distances, epsilon<gamma/(8b^2) permits a midpoint threshold. Calibration error, context matching, source drift, and replica-dependence errors must be added before invoking this bound. Full finite-data calibration and concentration remain to be supplied.

## 8. Why incompleteness remains real
Even if all local response equalities and pair moments are learned, the joint response vector may have different positive distributions with the same first two moments. A scalar Bernoulli probability P supported strictly inside (0,1) can have two different positive finite-support distributions with equal E[P],E[P^2] but different E[P^3]. Three simultaneous response replicas distinguish them; two do not. Further, identical one-time response-vector laws admit temporally persistent and independently refreshed sources. The paired protocol does not identify their temporal laws unless aligned across-time tests are included.

These ambiguities do not prevent Theorem 1: it needs only equality of response functions, which is exactly a second-moment question. They do prevent arbitrary assembly of higher-order or temporal claims. A main stress family should make this distinction explicit at growing system size, with nonlinear local closure discovered rather than supplied.
