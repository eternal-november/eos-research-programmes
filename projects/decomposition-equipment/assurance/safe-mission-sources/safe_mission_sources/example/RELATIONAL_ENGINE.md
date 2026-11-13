# Exact persistent-mechanism engine

`relational_engine.py` contains no plant generator, hidden-state access, motion
controller, acquisition policy or mission planner. Its inputs are declared
structural bounds and permitted observations. Synthetic unconstrained contexts
in the engine tests are not evidence of physically achievable acquisition.

## Declared hypothesis class

A response is a fixed Boolean function of zero, one, or two distinct port
features `[run(port) >= threshold]`, with threshold in `1..L`. Run counters are
observed action-derived state, capped at L. Both essential binary inputs must
actually affect the truth table. Increasing port order removes swapped aliases;
constants and unary functions have separate representations. The catalogue size
is `2 + 2*n*L + 10*choose(n,2)*L^2`. This class is supplied, not learned from finite
data. Actual ports, thresholds and truth tables are not supplied.

A hypothesis ID denotes one persistent response function. It cannot change from
one question or time step to another. A complete environment would select one
hypothesis for every response output, but the engine never lists that product.

## Evidence and relational factors

Coordinate evidence filters one domain. A sum diagnostic observes
`f_i(c) + f_j(c)` in `{0,1,2}` at a known counter context c. It introduces a factor
between persistent function variables i and j. Repeated observations on that
edge partition each local catalogue by its vector of Boolean answers.

For an edge with k observations, each signature is a k-bit integer. At every
position with observed sum 0, both endpoint signature bits must be 0; at sum 2,
both must be 1; at sum 1 the bits must be complementary. Thus a valid signature
has at most one compatible partner signature. The edge stores signature-to-local
candidate bitsets, not a quadratic table of candidate pairs.

The diagnostic graph is allowed to be any forest. It is distinct from the
unknown physical response scopes, which may overlap arbitrarily in command
ports. A new cycle-closing diagnostic raises `CycleError` before any mutation.
No result is claimed for loopy consistency from this engine.

## Exact checking argument

Each domain contains exactly the local functions surviving unary evidence and
neighbor support restrictions. Directed arc revision removes a function only
if its edge signature has no compatible surviving neighbor signature. Such a
removal cannot delete a complete model.

On a tree, a surviving value at any chosen root extends to a complete assignment:
choose a compatible child value for each edge and recurse into disjoint child
subtrees. Arc consistency ensures a compatible choice at every step. Components
are independent. Therefore nonempty arc-consistent domains are equivalent to a
coherent global model, and each surviving local value has a global extension.
This conclusion would not be sound for an arbitrary cyclic factor graph.

For a query, first intersect relevant domains with all specified output-value
constraints, retaining one function per response across all queried contexts.
Run exact forest propagation. Feasibility means at least one persistent complete
world satisfies the entire query. Universal conjunction checks rule out a
counterexample to every conjunct. They deliberately return false on inconsistent
evidence rather than using logical vacuity as a safety certificate.

Joint outcome enumeration is exponential in the number of queried coordinates;
it is explicitly a bounded caller operation, not a polynomial planning claim.

## Recursive interface extraction

For one response domain, take the union of its candidates' essential ports and
cap each corresponding run counter at the largest surviving threshold for that
port. `cap(run+1)` and resetting to zero commute with that cap, and every
candidate threshold test is preserved. This is a sound recursive observer for
all surviving local functions. It is not claimed minimal for a multi-output
mission, and constraints on energy, held commands or other responses may require
additional state. Unique scope/function is reported only when the domain
actually supports that conclusion.

## API

- `Catalogue(n_ports, L)`: build the canonical structural universe.
- `find(features, table)` and `describe(id)`: construct/inspect canonical test
  hypotheses. A learner need not call `find` on simulator truth.
- `ForestKnowledge(catalogue, n_outputs)`: initially unconstrained knowledge.
- `observe_coordinate(i, context, bit)` and `observe_sum(i,j,context,total)`:
  commit delivered evidence; return whether the resulting knowledge is valid.
- `copy()`: independent branch; the immutable catalogue/prediction cache is shared.
- `feasible(assignments, domain_restrictions)`: exact coherent-world query.
- `guarantees(assignments)`: universal conjunction with no-vacuity safeguard.
- `possible_coordinate`, `possible_sum`, `possible_vectors`: exact outcomes.
- `state_key()`: exact hashable state for policy memoization, ignoring duplicate
  evidence records.
- `discovered_interface(i)`: candidate/scoping ambiguity and safe counter caps.
- `metrics()`: catalogue/domain/signature sizes and explicit operation counts.

The byte metrics cover integer bitset payloads, not all Python object overhead.
They are not a total-memory benchmark. Signature count can grow to catalogue
size, and synthesis using this checker can still be exponential.

## Checks

`python test_relational_engine.py` runs eight tests, including catalogue-function
uniqueness, independent scalar evaluation, small complete-world enumeration for
random evidence prefixes, retained nonproduct complement relations, cycle
rejection without mutation, inconsistent-evidence handling, and recursive memory
cap preservation. `relational_engine_qa.json` records the frozen source hashes and
a larger planted-world retention smoke test. Full-world enumeration appears only
in the independent small test oracle, not in the production engine.
