# Observable diagnostic enrichment: finite executable check

31 October 2026. Run `python verify_observable_enrichment.py`. It imports only the three **relative, packaged** source copies in `observable_reference/`, originally from the existing shared-priority pipeline. Their SHA-256 hashes are recorded in `observable_enrichment_results.json`.

## Verified outcome

All **384** executions pass: all 24 four-job priorities, each with all 16 fresh observed batch words. The six priorities extending P={0<3,1<2} comprise **96** of these executions. Across those executions, the observable decoding map has image exactly the previously computed K_P; across all 384 it has image K_empty. At b=0011 the P-restricted image contains only y=11.

This is an enriched observable profile, not a claim that y was already observable in the old anonymous productive batch. It uses existing safe operations and additional authorized acquisition time. No hardware or callback fields change.

## Fixed public policy, scope, and costs

Before any observations, fix n=4, roles ABAB, public work upper cap 100, known request grid R=400, callback jitter J=0, and the pipeline's supplied processing allowances. Fix the entire diagnostic policy:

1. Existing singleton P and D calibration for each module (8 invocations).
2. For each of the six unordered module pairs in lexicographic order, call existing `Learner.before(i,j)`: atomically invoke D_i and P_j, then retain both anonymous reports (12 invocations).
3. Charge the compile allowance and wait until the predetermined T0=6400.
4. Admit the fresh all-ready four-job productive batch; the fixed deadline is 6820.

The pipeline's envelope gives local=3200, joint=3200, comparison bound=6, total invocation bound=24. It is computed from public upper bounds before commissioning. All runs use the identical request manifest and schedule. Acquisition finishes before T0; every command finishes before the deadline. The actual common intrinsic Q in these tests is 100. Processing allowance constants are supplied interface bounds, **not** Python benchmarks or a derived hardware latency guarantee.

P is a restriction on the tested family of worlds (the already retained comparisons). The new acquisition costs above are charged in full; this finite run does not replay or erase any separately incurred historical commissioning cost. If total lifetime cost includes historical records, that sunk cost remains additional.

## A decoder with no hidden-state inputs

The pure `decode` function accepts only:

- diagnostic raw `(time,bit)` reports;
- the caller's own request log `(start, module, operation, useful)`;
- productive raw `(time,bit)` reports;
- public caps, with fixed public roles and envelope as policy constants.

No service order, grant trace, callback identity, private priority, addressed output bit, simulator state, or `Learner.edges` is passed to it. The request log contains **requests the controller issued**, not response attribution revealed by the server.

The decoder remeasures Q from the singleton records, validates common P/D demands, derives each pair comparison from the first arrival's offset Q or 2Q, obtains the unique topological order, reads the rank-bit word from the fresh batch, and XORs those observed bits by the learned role order. This gives an actual runtime function

    eta(z) = (observed b, V(learned order, observed b)).

It never compares against an unavailable y-truth predicate. A separate test-oracle assertion checks the decoder's learned order against simulator priority, and its result against the pipeline's existing certificate-driven production command. This oracle check is not a runtime input.

Each raw record is serialized to JSON and decoded again; results remain identical. This checks that no object identity or hidden Python reference supplies the decoder's information.

## Support witnesses and pullback tests

For each oracle priority and desired rank word, the test harness preconfigures 20 diagnostic bits equal to zero and four module payload samples whose observed order is the desired word. This is an **oracle-only support witness coupling**, not a controller operation, pilot, or claim that bits are controllable. All 24 bits are a lawful finite fresh independent fair-bit realization, with probability 2^-24 conditional on the chosen priority. No distribution over priorities is asserted. Lags are fixed at zero, as required by the fixture.

For every tested raw record z and every target pair (b*,y*), the check compares

    [eta(z)=(b*,y*)]

with the oracle semantic response predicate. All **24,576** such pullback tests agree. Thus those predicates are computational tests on the enriched observable record, not hidden y-oracles. For every pi extending P and every b, one explicit lawful raw witness appears in the output. Conversely every displayed decoded response is V(pi,b). Their supports therefore match the enumerated K_P exactly on this fixture.

The finite executions establish the requested finite evidence. The general correctness argument still depends on the supplied common-Q, zero-jitter, persistent-priority, safe-diagnostic, fresh-bit, closed-horizon, and physical mission-bridge assumptions. These checks do not extend the comparator to nonzero jitter, unequal demands, arbitrary new contexts, or unknown scheduling policies.

## What this does not identify

The enriched record contains additional discriminating diagnostic information. It is not observationally equivalent to the old productive record and it is not free. Mapping enriched records to (b,y) forgets distinctions in the new raw diagnostics; it does not prove raw-profile equivalence or a same-cylinder comparison to the original tight-budget observation profile. The old conditional support middle and this new raw-profile middle must not be silently identified. The comparison is the explicitly defined observable result-predicate presentation/pullback, within the enlarged authorized execution envelope.

## Supplemental same-world replay of the retained old evidence

The main 96-case P subfamily restricts the priority parameter and relies on the earlier full-record fixture proof for the retained old E; it does not itself replay old E. A separate **six-run supplement now does replay it**, using the same persistent `Plant` throughout each run:

1. Run the eight singleton calibrations and the old two diagnostics D_0/P_3 and D_1/P_2, with all 12 diagnostic payloads zero. Retain their complete raw reports and the caller's request log. Charge the old compile stage.
2. Without replacing the Plant, resetting its clock, or resetting any server state, run all six new pair diagnostics. Reuse the established local work certificate, charge a second compile stage, and keep all new records.
3. At fixed absolute T0=7600, run the fresh productive batch with observed word 0011. The deadline, also predetermined, is 8020.

The policy pre-reserves 8 total comparisons, 24 diagnostic invocations, four productive invocations, and an extra whole grid interval of 400 for the old compile stage. The public envelope is therefore local=3200, joint=4000, extra-old-compile reserve=400, T0=7600, deadline=8020, maximum invocations=28. All six runs finish at 8012. Their old prefix ends at 4318, and **both the complete old raw records and old own-request logs are identical across all six priorities**. No old evidence is synthesized from private priority; it is emitted by executing the actual fixed old diagnostics in the simulator. Thus the new experiment genuinely continues each old compatible world rather than silently replacing it with a fresh one.

The decoder is given the publicly selected calibration plus new-pair stage records and the new public absolute T0. The old pair records remain retained in the full transcript; choosing stages for decoding uses only the caller's experiment log. It returns 11 in all six cases. The simulator's unchanged private priority is used only in the final oracle assertion. Each complete prescribed 28-bit realization has conditional probability 2^-28 under the fixture's fair independent bit law.

The supplement is recorded under `same_persistent_world_supplement` in the JSON. It verifies the original E-to-enriched-context continuation concretely for the strict-gain word; it does not turn the changed protocol into the old tight-budget protocol or erase historical costs.
