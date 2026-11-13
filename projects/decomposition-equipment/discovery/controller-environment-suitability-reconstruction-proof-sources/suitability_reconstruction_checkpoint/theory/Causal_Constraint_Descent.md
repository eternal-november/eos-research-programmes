# Recognizing conservative causal interface descent from actual record constraints

## What is recognized

The cut-capability theorem reduces causal implementation to simultaneous code equalities, actual readout dependencies and terminal response demands. This note eliminates a universal quantifier over code assignments from one important interface-descent question. It gives a terminating, independently checkable criterion on actual record-derived constraints, and constructs a finite driver-level counterexample when the criterion fails.

The exact property is POINTWISE conservativity: every assignment of codes to the coarse history/register points is valid exactly when its pullback is valid on the fine records. Thus passing preserves all such code assignments at every finite resource bound, and consequently their feasible resource spectra. The converse is not claimed: two descriptions could have the same feasible budgets but admit different implementations. Nor does the property cover fine controllers whose codes do not factor through the chosen coarse history map.

The information architecture is fixed: each physical primitive has explicitly permitted memory/readout input ports and output ports, and the same primitive table is shared across all its occurrences. Within these ports, finite update and decoder tables are unrestricted. Gate-limited sublibraries require additional implementation-preservation checks; the equality criterion does not grant arbitrary hidden inputs or new communication.

The proof mechanism is finite equality/Horn entailment. That logic is standard. The substantive extraction is from shared actual causal records, including cross-chart pairs and task-demand hyperpatterns, rather than a postulated strategy isomorphism or per-cut information partition.

## 1 A finite typed causal constraint presentation

For each memory type t let V_t be a finite set of code points. A point represents the memory at an ACTUAL available history/register-port occurrence. Different histories reaching the same environment state remain different code points. Actual same-prefix/chart anchors identify code points by equations. Named reset constants may be included as distinguished points; any required inequality between such constants is a forbidden equality pattern. Their numerical labels have no extra observable operations in this unrestricted-table fragment. Gate libraries or fixed arithmetic on named memory values are outside this equality-only recognition theorem. A code assignment is a family e_t:V_t→M_t into arbitrary nonempty finite register carriers.

A presentation P consists of:

1. Unconditional typed equalities E0 between code points, derived from actual shared-prefix anchors and reset consistency.
2. A finite family of Horn rules P_r⇒(u=v), where P_r is a finite set of typed input-code equalities and u,v have one output memory type.
3. A finite family of forbidden patterns F. Each F is a finite set of typed equalities; a code assignment violates F when it makes EVERY equality in F true. An empty forbidden pattern means no assignment is valid.

These constraints have the following direct operational extraction.

### Update rules from two actual records

Take two occurrences of the SAME physical primitive τ and two actual records at those occurrences whose delivered non-memory readout tuples are equal. If the code values at every permitted memory input port agree, the codes at every output port must agree. For each output port, add one Horn conclusion with those input equalities as premise.

All pairs are considered across the combined tagged union of occurrences, not separately within each local chart. This is exactly the condition that one deterministic τ-table extends the required actual input/output rows. No code variable for a hidden field absent from τ's physical input is introduced into the premise.

### Terminal patterns from actual task demands

Fix one physical decoder and one delivered non-memory input value. Each actual terminal record has a permitted action set A(w) in a fixed nonempty finite action alphabet A. If some collection of such records has empty intersection of its A(w), they may not all give the same tuple of memory inputs to that decoder. Add the forbidden pattern that equates their code points port by port.

It suffices to examine collections of at most |A| records. If an intersection is empty, for each a∈A choose one record excluding a; these at most |A| records already have empty intersection. A one-record empty action set generates an empty pattern and is correctly impossible. Pairwise compatibility alone is insufficient in general.

After all update and terminal constraints are extracted, satisfying P is equivalent to the existence of the required unrestricted tables on the permitted ports: update rows form functions, and every decoder input has a common admissible action. Total extensions on unrealized input rows can be chosen freely. This is the finite-table reconstruction argument, not a claim that arbitrary hardware libraries realize every such extension. An empty action alphabet for a required total decoder is rejected as a separate interface error; the bounded-hyperpattern argument assumes A is nonempty.

## 2 Fine and coarse interfaces

Suppose actual record maps and history/register-port maps are supplied from a fine description to a coarse one. They preserve physical primitive identifiers, input/output port types and task meanings. Fine readout equality implies coarse readout equality; coarsening can merge additional readouts or admit additional record combinations. The controller codes under comparison are coarse code assignments pulled back along the supplied history maps.

Translate every fine constraint to the coarse code-point sets V_t by those maps, obtaining P. Let Q be the constraints extracted directly from the coarse actual records. Assume the maps have been checked to give the easy direction

    every Q-valid assignment is P-valid.             (Forward)

For ordinary task-preserving readout coarsening, this follows directly: each fine actual row has its prescribed coarse image; same fine readouts remain same coarse readouts; fine bad action intersections map to coarse bad intersections. If more general interface changes are allowed, Forward must be established from their actual tables, not assumed from the word “abstraction.”

The question is whether P-valid implies Q-valid for EVERY choice of finite carriers and EVERY code assignment. This is not the demand that every coarse record has a particular fine lift. Redundant bad records can impose the same constraints, and fine equality chains can force a coarse equality without any single synchronized pair lifting it.

## 3 Equality closure with forbidden patterns

Given a finite set H of additional assumed equalities, compute Cl_P(H):

- start with E0∪H and take typed equivalence closure;
- whenever every equality in a Horn premise P_r is present, add its conclusion;
- again take equivalence closure and repeat until no change occurs.

There are finitely many code points, so this terminates. At most sum_t max(0,|V_t|−1) successful class mergers occur after initialization, though a straightforward implementation may scan many redundant rules. This is a termination bound, not a polynomial bound on the potentially large record-derived presentation.

Call the closure inconsistent when it contains every equality of some forbidden pattern F of P. Otherwise it is consistent.

### Lemma 1 Canonical separating code assignment

If Cl_P(H) is consistent, assign each code point its equivalence class. This is a finite P-valid code assignment satisfying H. Each carrier needs at most max(1,|V_t|) values. If a typed pair u,v is not in the closure, this assignment gives it different values.

Proof. Equivalence closure satisfies the initial equalities. Closure under every Horn rule proves all update implications. Consistency says that no forbidden pattern has all its equalities true. If a type has no points, choose a singleton carrier. Distinct equivalence classes remain distinct. QED.

If the closure is inconsistent, no P-valid assignment can satisfy H, since every P-valid assignment respects each step of the closure construction.

## 4 Exact descent theorem

**Theorem 2 Pointwise causal descent criterion.** Subject to Forward, P and Q have the same valid code assignments on EVERY finite family of register carriers if and only if the following finite tests pass:

- For every unconditional equality u=v of Q, Cl_P(empty) either is inconsistent or contains u=v.
- For every Horn clause H⇒(u=v) of Q, Cl_P(H) either is inconsistent or contains u=v.
- For every forbidden pattern F of Q, Cl_P(F) is inconsistent.

Proof of sufficiency. Let e be P-valid. It respects all P closures. For a coarse Horn rule whose premise holds under e, the corresponding closure cannot be inconsistent, so its conclusion belongs to the closure and holds under e. The unconditional case is the empty premise. If a coarse forbidden pattern were true under e, e would satisfy its assumed equalities, contradicting the required inconsistency of Cl_P(F). Thus e is Q-valid. Forward gives the reverse implication.

Proof of necessity and explicit obstruction. If a coarse equality or Horn test fails, its closure is consistent and omits the desired conclusion. Lemma 1 gives a finite P-valid assignment satisfying the premise and falsifying that conclusion. If a coarse forbidden-pattern test fails, its consistent closure gives a finite P-valid assignment making the whole forbidden pattern true. Either assignment is a concrete counterexample to pointwise descent. The finite-table reconstruction then supplies actual fine update/decoder tables on their permitted inputs; the failed coarse clause explains why those SAME encoded causal requirements cannot be implemented at the coarse interface. QED.

The counterexample is not automatically a proof that NO other coarse controller works at that budget. It refutes preservation of this valid encoded implementation. Likewise the finite closure criterion is exact for all carrier sizes at once. For one very small fixed budget it can be stronger than necessary, because its canonical separating assignment may require more states than that budget permits.

Nonvacuity is checked separately. A consistent Cl_P(empty) constructs at least one finite fine implementation; an inconsistent one means the fine constraints already have no implementation. The descent theorem must not be used to call such an empty problem a successful robot/environment match.

## 5 Genuine mixed constraints and gluing

Suppose two chart/presentation fragments are joined along actual shared history/register points and physical primitive identifiers. Their combined P contains all original clauses plus:

- new anchor equalities at shared prefixes;
- update implications formed from one actual row in one fragment and another row in the other fragment using the SAME physical primitive;
- terminal forbidden patterns whose records come from several fragments but feed the SAME physical decoder input.

The new update clauses are derived from pairs of actual records, and terminal obstructions need at most |A| records, even when the number of charts is unbounded. This does NOT imply a fixed bound on the length of a global equality chain: cyclic chains of forced identifications can still be arbitrarily long.

If each separate fine-to-coarse fragment is conservative, its old coarse clauses remain entailed after adding the fine mixed constraints. Therefore the combined quotient is conservative exactly when all newly introduced coarse mixed clauses pass Theorem 2 using the combined fine closure. This is an explicit mixed-interaction criterion. Merely checking the fragments independently, or merely observing that their separate code spectra agree, is insufficient.

The tables in this theorem have been existentially reconstructed. It does NOT by itself preserve a supplied literal table in arbitrary new sharing contexts. The separate Parametric_Causal_Descent theorem retains the physical function symbols and decoder demands to obtain that stronger context-safe statement.

Under composition of two already certified interface changes, pointwise conservativity composes by pulling back the same code assignments twice. This gives arbitrary finite chains. For original typed substitution, a presentation theorem must additionally prove that the actual substituted shared-table and decoder constraints are exactly the generated within-slot and mixed constraints described here, with occurrence addresses and boundary transports retained. This note does not substitute temporal concatenation for that spatial proof or claim coherence for unlisted semantic cuts. The direct gluing argument applies to fresh code points, explicit port identifications and conjunction of the extracted constraints. Existentially hiding auxiliary stores is a different operation and needs a separate projection theorem; it is not licensed by the same proof.

## 6 Relation to synchronized witness lifting

A stronger objective condition is often convenient: every coarse same-readout pair of actual rows has a fine pair with the specified history endpoints and ONE shared fine readout, and every coarse bad terminal record collection has a fine collection sharing the prescribed decoder input. Such synchronized fibre-power lifting implies the relevant clause tests directly. Separate lifts with different fine readouts do not suffice.

But raw synchronized surjectivity is not necessary for semantic code conservativity. A coarse equality can already follow from a chain of fine equalities. A coarse forbidden terminal pattern can already contain a smaller projected fine forbidden pattern, or become inconsistent through update closure. Theorem 2 captures these redundancies exactly. Thus actual witness recovery and preservation of the causal capability constraints are distinct requirements, just as retaining whole records is stronger than retaining only one selected behavioral verdict.

Without update Horn clauses, the terminal-only specialization reduces to equality of the upward-closed families generated by projected forbidden patterns. With one code input per decoder, these are the usual forbidden hyperedge clutters. With deterministic two-valued tasks, pair conflicts suffice; with general action sets, they do not. The full theorem adds actual shared-table update consequences and their interaction with those terminal demands.

## 7 Boundaries

This is a structural recognition theorem for finite actual cut/record presentations, not a general distributed-synthesis decision theorem. It does not reconstruct absent physical observations, infer an unknown world from data, establish probabilistic guarantees from support alone or minimize arbitrary gate-constrained controllers. It preserves q-compatible code assignments and their causal realizability, not every fine controller irrespective of what information it uses.

Its role in the larger program is to supply an independently checkable descent test and explicit failure certificate from the typed witnesses, rather than assuming “strategy descent.” Standard Horn/equality reasoning performs the finite closure; the actual decomposition, sharing and information constraints determine which clauses exist and which mixed clauses must be checked.
