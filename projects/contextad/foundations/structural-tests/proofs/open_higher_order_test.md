# Open higher-order test: generative callback tickets

Status: worked operational benchmark and explicit preservation obligations, not a new expressivity theorem or adopted contract. This is one family, parameterized by arbitrary finite client syntax and arbitrary finite observation depth. It is not a finite closed test suite masquerading as a universal theorem.

## 1. Interface and contexts

A separately compiled library exposes an abstract type `Ticket` and:

```
new  : Unit -> Ticket
same : Ticket * Ticket -> Bool
run  : Ticket * (Unit -> Unit) -> {Done, Spent}
```

The client language is sequential call-by-value with functions, products/sums, Booleans, recursion, mutable client-owned references (including references storing callbacks and tickets), and `emit : Bool -> Unit`. Clients may copy tickets and closures, compare tickets only through `same`, retain them indefinitely, allocate other tickets inside callbacks, and reenter `run` through any ticket they already possess. There is no ticket constructor, address arithmetic, reflection, private-store read, thread, timing observation, finalizer, or first-class continuation. Allocation never exhausts. These restrictions specify an ordinary abstract-data-type interface; they do NOT rule out reentrancy, aliases, nontermination or the distinguishing context below. Opaque tickets are not uncopyable linear values. Their *use permission* is one-shot.

`run(h,k)` checks h. If spent, it returns Spent without calling k. If live, it irreversibly consumes h BEFORE calling k once, waits for k to return, then returns Done. If k diverges, this run does not return and h remains spent. Client exceptions are omitted rather than silently assuming rollback; an exception extension must explicitly propagate without resurrection.

Observations are finite prefixes of client `emit` events, public library calls/returns, and library-to-client callback entries/returns, with public ticket identities considered up to a consistent bijection. Termination is a separate marker. Keeping call/return events makes this stronger than endpoint agreement. Internal allocation addresses and administrative reductions are unobservable. A finite prefix can end while a callback is running. No claim about real-time latency is made.

Quantification: for EVERY well-typed closing client context C at this interface and EVERY finite observation length n, not merely every context generated up to a fixed testing depth. Code size, number of allocated tickets, recursion depth, and number of callback uses have no common finite upper bound. A particular run prefix still has finite support.

## 2. Two positive implementations and an adversarial rival

Implementation A allocates a fresh private Boolean cell per ticket. The ticket is an opaque object carrying that cell. `same` compares identity. `run` tests the cell, sets it false before invoking k, then returns Done. Its local state is distributed across the allocated objects.

Implementation B allocates distinct private numeric IDs and stores their status in a private finite issued/spent table. A ticket is an opaque ID wrapper. `same` compares IDs. `run` checks/updates the table before invoking k. Its local state is centralized. Natural-number arithmetic and table lookup are internal, not methods available on tickets. B is legitimate; no ban on a monolithic state encoding is being used to manufacture an obstruction.

Implementation L is A except that it sets the cell false AFTER k returns. The following well-typed finite client distinguishes L from both positive implementations:

```
h = new();
run(h, lambda () {
    run(h, lambda () { emit(true); });
});
```

A/B: the inner run returns Spent, no `true` is emitted. L: the inner callback emits `true`; both invocations eventually return Done. This is legal use of an exposed alias, not authority forgery. More generally, nesting d such invocations yields one callback entry per ticket in A/B and d entries in L. Thus a quotient retaining only a ticket's final spent state and the outer Done result identifies programs whose allowed interaction traces differ. The claim is about that particular quotient, not about all state-based semantics.

## 3. Canonical open protocol machine

Use an infinite atom supply H. Canonical private state is a finite map `s:H -> {live,spent}`. Client configurations carry code, environments, their own store and an evaluation stack. The stack includes suspended service frames `ReturnDone(h)`. Public events may carry ticket atoms and opaque callback references; callback references point to client closures, never to a semantics oracle.

Transition rules at service boundaries:

* new: choose fresh h, extend s by h:live, return h.
* same(h,g): return h=g, leaving s unchanged.
* run(h,k), s(h)=spent: return Spent, no callback frame.
* run(h,k), s(h)=live: update s(h):=spent, push ReturnDone(h), transfer control to k and emit callback-entry.
* callback return: pop that frame and return Done.
* all client computation uses the ordinary evaluation stack; another run can push another frame before earlier frames return. Allocation inside any callback extends the same finite world.

Every service operation terminates internally up to its intentional callback transfer. Hence private administrative reductions cannot add an infinite silent computation. Public freshness is generative: fresh names may be consistently permuted without altering observations. This is a protocol semantics with higher-order client code, not a state transformer treating `run` as an atomic black box.

## 4. Representation-changing comparison: worked proof

A world W is a finite partial bijection between A's allocated ticket identities and B's issued IDs. For every paired ticket (a,b), A's Boolean is true iff B's status is live. All allocated tickets, including currently unreachable ones, may be retained in W; garbage collection is outside the test. This is a ghost relation used in a proof, not data supplied to the client.

Relate client configurations by the same source client code under the respective fixed API-wrapper translation and corresponding stack shape, replacing each ticket a with W(a); ordinary client references are related by a separate allocation bijection. Related closures have the same source code under the respective fixed wrapper translation and related captured environments. Related client heaps have corresponding reference contents, including stored closures. This can be defined by a finite graph isomorphism of the reachable environment/store graph, not recursive unfolding of possibly cyclic heaps. Suspended service frames have paired tickets and the same callback return position. It is necessary to retain the stack and the store graph, not just the final Boolean table.

**Lemma (one boundary step).** Related configurations have matching next visible events and weakly matching next configurations, extending W only when fresh tickets are allocated.

Proof cases:

1. Client beta-reduction, branch, and store operations: identical code chooses the same branch because all observable base values agree; reference updates preserve the client-heap graph relation. New client references extend their bijection. Capturing or storing a callback preserves the graph relation, including cycles.
2. `new`: A chooses a fresh cell a; B chooses its next unused ID b. Extend W by (a,b). Freshness makes this a bijection and preserves every old alias/equality. Neither concrete allocator needs to choose the same raw address.
3. `same`: injectivity of W gives a=g iff W(a)=W(g).
4. Spent `run`: the state invariant gives Spent on both sides; no callback is entered.
5. Live `run`: both implementations update BEFORE yielding; paired statuses become spent and paired ReturnDone frames are pushed. Captured callbacks are related by the client graph relation. Crucially the invariant already holds when the context regains control, so arbitrary reentrancy invokes the same cases again rather than requiring an assumption that the callback is harmless.
6. Callback return: paired frames pop and produce Done. Nonreturning callbacks have matching finite observable prefixes but no forced Done; a silently diverging callback can produce only finitely many observable events.

All implementation-only work between these cases is finite and produces no observations. These cases establish a weak boundary bisimulation and permit the induction to continue after every callback.

**Theorem (uniform contextual replacement).** For every C and n as above, A and B generate identical length-at-most-n observation prefixes modulo the growing ticket bijection. Their terminating executions correspond. Proof: instantiate the initial empty world and iterate the lemma; for termination and divergence reflection, use the matched client reductions of case 1 together with finite administrative progress and paired stack completion. Boundary-event bisimulation alone would not suffice, because it could hide infinite silent computation. Conversely use the symmetric lemma. For diverging runs the finite-prefix assertion does not assert eventual termination. This is an operational proof argument for contextual equivalence for the specified interface and operational observations, NOT a full-abstraction theorem for an arbitrary target language.

**At-most-once safety.** For each fresh h, at most one callback entry attributable to a successful run(h,_) occurs, across all prefixes, aliases and reentrant calls. Proof: only the live case can emit that entry and it changes live to spent; no rule returns spent to live. Aliasing does not create a new state entry. This theorem is uniform in all clients and allocation sizes.

## 5. Separate compilation and the structural test

The client compiler is fixed on OPEN syntax. It preserves lambda/application, recursion, reference operations and emit, and maps the three API operations to the corresponding implementation's wrappers. It is not chosen after inspecting the closed linked program. At an abstract interface it translates ticket occurrences uniformly, including occurrences in closure environments and stored callbacks.

For one-hole typed syntax contexts, capture-avoiding substitution gives the syntactic plugging equation

`compile_i(C[M]) = compile_i(C)[compile_i(M)]`, i=A,B.

This follows by induction on context syntax, with the binder case requiring the ordinary fresh-variable convention. It is not, by itself, a semantic representation theorem. The boundary bisimulation above supplies the semantic part: its action on configurations restricts to the same world/heap/stack transport on both sides of the plugging equation. Worlds are extended during execution, not reset when a separately compiled subcomponent is invoked. Thus a component M that stores a ticket then supplies a closure to a separately compiled C preserves the SAME alias and status relation after C reenters M.

A proposed contextad or mixed-context/content encoding should now supply a *single* semantic interface object and an interpretation of these open components, with:

1. the handle and callback interface preserved (no whole-program replacement by an untyped global-state result);
2. composition/substitution mapped coherently, with the same boundary comparison on nested plug-ins;
3. private-name extension and client-heap/closure transport respected;
4. the A/B comparison preserved, including suspended callbacks and intermediate spent status;
5. L distinguished by the exhibited context;
6. no observational access added to private locations or table IDs.

A lax/pseudofunctorial comparison is allowed if its comparison cells and their observable meaning are stated and its unit/associativity laws checked. No demand for literal equality of concrete heaps is imposed. Conversely merely defining a closed-state denotation after linking does not meet items 1-4. An encoding with a global heap CAN meet all six if it gives the fixed open translation and these comparisons. This test therefore targets interface/composition preservation rather than semantic computability.

We have supplied the operational comparison and syntactic plugging lemma, not constructed an interpretation functor into a particular contextad. Consequently this is a sharper test ready to apply to candidate categorical encodings, not evidence that those encodings fail or that a new categorical structure is required.

## 6. Strongest existing baseline, not a strawman

Ahmed, Dreyer and Rossberg, *State-Dependent Representation Independence*, POPL 2009, is directly relevant: its possible-worlds treatment supports local state and generative abstract types; Theorem 4.2 is the fundamental compatibility result and Theorem 4.3 gives contextual-approximation soundness. Section 5.6 explicitly studies reentrant callbacks with a lock. Our monotone spent-bit invariant is simpler than that section's temporary locking problem. Thus reentrancy/generativity alone cannot be advertised as a new gap. Mapping this example into that language requires an explicit encoding of opaque ticket identity and the chosen observations; the paper is not being claimed to prove our exact event-trace theorem verbatim.

Primary paper checked at theorem and example level:
https://home.ttic.edu/~amal/papers/sdri/main.pdf
Author resource page:
https://home.ttic.edu/~amal/papers/sdri/

A nominal higher-order operational model with a global heap, explicit continuation stack, and abstract names passes by the construction above. A relational/possible-world proof discipline supplies the right kind of representation relation. A callback-aware game or interaction semantics is also a plausible baseline, but no exact fully abstract game model or embedding theorem was checked here, so no such theorem is claimed. An atomic state transformer that hides callback transfers fails only if its observations/composition actually erase the interaction illustrated in section 2. State transformers with reified continuations or open resumption structure are not refuted.

## 7. Why the previous three controls do not test this

* Finite dynamic capabilities had a known finite slot store and no arbitrary client callback or stored higher-order value. Allocation/guard correctness there does not establish a world-extension theorem for all open contexts.
* Persistent shared randomness tested adaptive first-order observation histories, not arbitrary callbacks closing over shared aliases or semantic plugging of independently compiled clients.
* Partial recovery tested closed known atomic operations and their relations, with no control transfer while a library operation was in flight. Endpoint recovery compatibility cannot certify invariants at callback boundaries.

The new family does not need larger numerics. Its harder quantifier is one interface/comparison for every separately compiled client and every finite interaction depth, with fresh aliases and nested control transfer. The useful output if established contextad machinery passes is an actual open-composition preservation theorem; if it fails, the failure must name which required square or coherence fails and whether the baseline model still passes. A detected programming bug in L is only a sanity discriminator, not a research-level impossibility theorem.

## 8. Executable sanity witnesses

`check_open_higher_order.py` runs 200 A/B comparisons at nesting parameters 0–99, with and without fresh nested-ticket allocation; it checks alias equality, distinct fresh identity, callback traces and at-most-once entry. It also distinguishes late consumption in 99 nested contexts. `open_higher_order_results.txt` records the successful run. These tests do not enumerate the full typed language, cyclic closure stores, recursion or divergence; they are regression witnesses for the operational proof, not its substitute.
