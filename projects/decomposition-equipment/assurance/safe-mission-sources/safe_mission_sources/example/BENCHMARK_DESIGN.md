# Reset-free learned-interface mission benchmark (design, not results)

## Chosen implemented subclass

The implementation will be deterministic and finite-memory, rather than a claim to
solve stochastic mobile robotics. There are labeled actuator commands and readout
channels but no supplied actual dependency scopes or local transition tables.
Each unknown readout is an arbitrary Boolean table of at most two unknown
run-threshold features `(port, threshold)` with thresholds at most L. Tables,
ports, thresholds and useful recursive observer states are discovered from
permitted action/readout records. Truth is isolated to the plant generator and
scorer. Candidate mechanisms remain fixed for a complete run.

The Boolean readout has an explicit abstract actuator meaning: a high response
certifies a stronger braking envelope for a particular guarded passage; low
response supplies only the coarse envelope. The response-to-braking map and the
finite-memory universe are declared physical-contract premises, not discovered
facts. Bay stationarity makes preparation actions safe; this is an initial safe
capability, not an unexplained globally informative oracle.

## Physical and acquisition execution

The robot starts stopped in a protected bay. It must execute and pay for L
all-off ticks to initialize its observer. No reset or history injection occurs
later. Each bay permits changes to only a subset of command ports and reveals
only selected diagnostic readouts. Held commands and capped run memories persist
through movement. A diagnostic readout need not be available at the entrance to
the passage that uses it. Slow travel between accessible bays is independently
certified, but uses time and energy.

A fast passage is a complete timed motion option: acceleration, cruise and braking
must all satisfy the guard contract; check the predicted guard at every source
tick of the option, not just the endpoint. A slow option uses the global coarse
braking bound. Both options make actual positive distance progress to a new
protected bay, unlike the preceding requested-speed-only example. Deadline and
energy costs include initialization, preparation, observations, slow acquisition
travel, fast travel and terminal arrival. Stopping/aborting is safe but is not
mission completion.

## Discovery and planning

For each readout, maintain all sparse local hypotheses consistent with accessible
records. Never construct a list of complete environment models. A query is
certified only if every surviving local hypothesis agrees on its response; each
hypothesis retains its identity across future queries and observations. Unknown
scopes must remain ambiguous when records do not identify them.

A mission compiler should use goal-critical local hypotheses and their shared
input-memory interfaces. The first implementation can use bounded search and
explicitly charge that cost. It must not advertise polynomial-time global
planning. A small exact belief-state reference will test selected diagnostic
instances. A safely unreachable identifying observation must remain unavailable,
not be supplied by a test hook.

## Frozen comparisons to define before outcome runs

1. Learned local mechanism/observer policy, with all costs included.
2. Same hypothesis class and information represented as uncompiled local
   candidate sets: tests the value of compiling resolved interfaces separately
   from generic active learning. It may have equal capability.
3. Supplied true scopes but unknown tables/memory, same physical access and data:
   a serious structure oracle and an acquisition-cost ceiling, not a straw man.
4. A safe coarse-envelope transport policy under the same deadline/energy.
5. Full joint persistent-model reference on small instances where enumeration is
   feasible; equal information must give equal attainable capability. Its purpose
   is correctness and representation cost, not a claim that decomposition beats
   an information-equivalent optimal controller.

Hold out mission destination/order combinations rather than merely replay seeds.
Report actual completed goals by deadline, total acquisition and movement ticks,
energy, safety violations, refusal/timeout counts, candidate counts and eliminated
constraints, discovered scope/memory ambiguity, storage, and synthesis work.
Seeds, instance construction and task splits must be fixed before outcomes.

## Nontriviality gates

- Reject an instance solvable by one scalar threshold or setting all ports on.
- Include nonmonotone truth tables and competing command histories.
- Include a task where safe probing consumes an opportunity and where selecting
  the relevant tests matters.
- Include an inaccessible-information pair showing that safety cannot imply
  useful completion without a safe distinguishing opportunity.
- Include a small exact reference check and a growing family.
- Do not claim unique physical ownership from sparse functional scopes.

This document is a design contract. No empirical outcome is recorded here yet.

## Revised main uncertainty target

The independent-coordinate proposal above was retained as a baseline, not the
main heterogeneous-information claim. Joint diagnostic observations give the
sum of two response coordinates at a known history. They create relational
constraints between persistent local mechanisms. The supplied diagnostic wiring
is not claimed to be a discovered physical decomposition. Actual functional
response scopes and memory remain unknown.

The exact implementation represents each local candidate set plus an edge table
of its response signatures at all observed contexts. The diagnostic constraint
graph is required to be a forest; cycle-closing data are explicitly rejected.
Arc consistency is exact on that forest and retains its edges for subsequent
conditioning. It does not replace the relation by its projected marginal sets.
The implemented queue algorithm's measured work is reported; no claim that it
achieves the theorem's separate optimal two-pass asymptotic implementation is made.

The constructed growing OR/XOR residual family demonstrates complete timed
missions and known-scope/joint-reference agreement, but is deliberately simple
after identification. A separate frozen arbitrary-table partial-acquisition
family retains multiple scopes, memory thresholds and table alternatives and
compares coherent and rectangular whole-tail certificates. Those diagnostic
trials alone are not sequential mission executions. A separate AND-OR mission
compiler is being evaluated to join such evidence across an actual shared-budget
mission; failures/refusals are valid outcomes, not reasons to change the seeds.
