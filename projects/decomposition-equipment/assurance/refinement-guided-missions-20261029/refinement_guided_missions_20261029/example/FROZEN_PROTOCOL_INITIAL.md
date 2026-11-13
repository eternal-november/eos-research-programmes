# Delayed resource mission preregistration

Frozen before outcome runs on 29 October 2026. Implementation checks may expose
bugs; corrections will be documented rather than silently selecting successes.

## World class and supplied assumptions

Commands represent normalized actuator effort. Integer coefficients G represent
physical coefficients G/4. Each output has at most s nonzero input/lag cells,
coefficient alphabet {0,1,2,3,4}, lags 0 through L. Coefficients persist through
all acquisition and missions. Outputs are fully sensed. The actual support,
weights and delays are hidden from the learner. The generator supplies the
plant only; learners obtain observations through an execution interface.

Physical additive load uncertainty is at most 1/256. Sensor error is at most
1/256, giving total observation error at most 1/128. Capacity is 6/4 + 1/256,
so the robust nominal integer load limit is six. Safe pulse amplitude is 1/4:
the measurement grid spacing is 1/16, strictly exceeding twice total error.
A singleton pulse needs one command tick plus L all-off tail ticks. For a
scaled whole schedule, s <= 5 gives nominal peak at most 5/4, below capacity.
Shared power is floor(n/3), at least two. Commands are binary during service,
with no actuator used by two simultaneous stages.

Initial history is justified all-off. An additional explicit L-tick startup
flush is charged. Every later probe and service ends with its full lag tail;
there are no free resets. Diagnostic effort does not count as stage completion:
a stage requires uninterrupted nominal unit effort with the work fixture
loaded, while diagnostic mode is unloaded. This is a supplied service contract,
not a discovered physical property. Diagnostic mode switching has zero time in
this synthetic model; no hardware-timing claim follows.

## Fixed instance dimensions

Dimension triples (n, L, s): (6, 2, 3), (10, 3, 4), (14, 4, 5).
Number of outputs m equals n. World seeds: 202610292300 and 202610292301.
Each row has exactly s generated nonzero cells with at least two distinct inputs
and two distinct lags. The class supplied to learners remains at most s, not
exactly s. Coefficients are independent uniform integers 1 through 4.

Every world receives six sequential mission batches. Two load regimes are
retained for every world: roomy and tight. No seed is discarded for failure.

## Useful workloads and deadline accounting

Each batch contains max(2, floor(n/3)) jobs. Each job has two or three ordered
stages. A stage lasts one to three consecutive service ticks and has two
alternative actuator modes. A mode uses one actuator or a pair of distinct
actuators, with equal unit effort throughout its duration. Modes, durations and
job releases are generated independently of hidden kernel values. Multiple jobs
may overlap. Releases are integers zero through three. The planning grammar
includes all legal mode/start-time choices; all-off cannot satisfy positive jobs.

Let total stage work be the sum of stage durations, counting each stage once
rather than actuator multiplicity. Roomy service allowance is 2*work + L + 6;
tight allowance is work + L + 4. Job due times are the batch allowance minus a
public random offset zero through three, never below their release plus their
own total durations plus L. All delays remain public to the learner.

The first batch receives an additional public commissioning allowance
A = L + n*(L+1). Later batches do not receive that allowance. Its value is based
on dimensions before results, not actual acquisition. The actual startup,
probing, rehearsal, service and tail ticks are charged to the same batch clock.
Batches arrive sequentially on completion or explicit safe refusal; future
workloads are hidden until arrival. Refusal does not count as completed work.
Knowledge persists across batches and no plant reset occurs. Every successful
batch ends at zero command history after its charged tail.

## Common planner and independently checked certificates

All methods use the same finite mode/start-time MILP grammar and solver limits:
10 seconds per proposal and at most 2*n+12 proposals per batch. Float MILP
results are proposals, not independent proofs of optimality or impossibility.
Every accepted schedule is rechecked with integer arithmetic for stages,
precedence, occupancy, releases, deadlines, power, full-tail capacities and
resource accounting. Timeout and backend infeasibility have separate statuses;
no solver status alone is called mathematical impossibility.

A failed proposed schedule is not proof that no robust policy exists. Unknown
columns may be queried from its retained-model counterexample; after a known
failure the method replans. The fixed-schedule grammar is not all feedback
controllers. There are at most n distinct singleton queries across the entire
stream, but neither n total iterations nor inevitable completion is claimed.

## Compared acquisition and inference protocols

1. Local column refinement: exact singleton-identified columns, local sparse
   convolution, and exact top-k robust envelope for its retained column summary.
   Full execution observations are stored, but unrepresented extra equations
   are not claimed to be reflected by that envelope.
2. Dense column reference: same records, query choices and column summary,
   optimized dense arithmetic/common solver. It must match certified capability;
   no information-theoretic superiority claim is made.
3. Cached column refinement: all linear observation equations, exact rational
   row-space reuse, and independently checked LP-dual response bounds; it may
   infer across missions before asking for another singleton query.
4. Cached scaled rehearsal: all equations and the same inference machinery;
   uncertain proposed schedules can be safely rehearsed at amplitude one
   quarter. Unsafe measured patterns yield sound monotone exclusion cuts.
   This declared query strategy is not claimed optimal among all mixtures of
   rehearsal and singleton queries.
5. Known-kernel reference: actual coefficients supplied, same job grammar and
   planner, acquisition-free reference. Its physical trajectory is still checked.

Cached LP bounds retain nonnegativity, coefficient bounds, exact observation
equalities, and the valid row-mass consequence sum(G) <= 4*s. This is a sound
relaxation of support count, not an exact sparse-version-space solver. Integer
objective rounding and optional independently validated sparse counterexamples
may sharpen it. A relaxation timeout/loose bound is not a proved necessity to
rehearse. Store the limitation and extra query count explicitly.

All methods receive the same class/noise/power promises and can retain all raw
records. Dense column equivalence is a representation sanity test. The cached
methods test whether additional retained information changes acquisition cost.
No universal lower bound on dense inference or cached rehearsal is claimed.
A long rehearsal may identify many or all columns at once.

## Required outputs

Keep every world/batch/method result, including unsafe rejected proposals,
refusals and timeouts. Report completed batches/jobs, all acquisition/service/
tail ticks, diagnostic energy, number of column probes/rehearsals, retained
matrix rank, coefficients/support identified, certificate work, solver work and
storage. Report cumulative cost and crossover only for the declared protocols.
Store exact traces/configuration and sufficient independent replay data.

The prior connected delayed-role path is a separate positive strictness law
check, not the main workload. It establishes a capability gap only for its
stated coarse summary. Small exhaustive checks validate that law; the main
random family may show ties or negative results. No outcome-dependent retuning
or new favorable-seed search is authorized by this protocol.
