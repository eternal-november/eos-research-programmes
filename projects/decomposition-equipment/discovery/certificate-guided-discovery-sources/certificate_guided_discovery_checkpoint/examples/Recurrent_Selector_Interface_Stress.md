# Recurrent selector family: a persistent interface stress test

## Plain-language abstract

Two useful ways of packaging a running system can each obey the same communication budget, while implementing both descriptions through one finer packaging exceeds that budget. This example uses a selector that reads one of many changing peripheral bits. Packaging half of those bits with the selector halves the necessary incoming message. Two crossing choices of which half to include can each work, although their intersection leaves the selector needing all the bits. The obstruction is not lack of a mathematical intersection or lack of state information in the whole system. It is the inability to implement that intersection through the admitted interface. The example is an exact, scalable stress test of certificate composition, not a theorem identifying a physical architecture from observations.

## 1. Declared model and all-step dynamics

Fix r >= 3, N=2r. The state is (s,y,v), where s is a selector in {0,...,N-1}, y is a bit, and v is an N-bit peripheral vector. All initial states are admitted. Define synchronous dynamics

    y' = v_s,
    s' = (s + 1 + y) mod N,
    v_j' = v_j XOR (y AND v_(j+1 mod N)).

The peripheral ring and selector interact recurrently: y affects every peripheral update and selector motion; a selected peripheral affects future y and hence their future evolution. For N>=2, the global transition is not a Cartesian product over the central and peripheral coordinates. There is no reset operation. No operation reports a membership partition.

The candidate local mechanism has O(N) Boolean gates, plus a selector/multiplexer of size O(N) and log(N) selector bits. Its explicit whole-state table has N*2^(N+1) rows. Mechanism-certificate size and whole-state enumeration are therefore sharply different.

The formula is a supplied candidate mechanism within a declared model universe. Its consistency with given finite readouts can be checked by a trace witness. That does not establish that the unknown environment has this mechanism. The all-step implementation certificates below establish exactness for this candidate, for every initial state and every time. They are not finite-trace fitting claims.

## 2. Exact interface contract

Each synchronous round has one simultaneous message from each block to the other. An encoder may be any deterministic function of its own current block state. It cannot inspect the receiving block's current state before choosing that round's message. The decoder has its own current state and the received message. The interface bound for a block is the logarithm base two of its TOTAL incoming message alphabet, rounded up. In a two-block cut this is one message; in a finer cut it is the joint tuple of all incoming messages, not a separate allowance for each neighbor. Copies of a bit inside a block are free; communication between blocks is charged.

This is a one-round distributed implementation contract. It is substantive, and is NOT an unconditional physical restriction. Section 6 explains exactly how interaction or sensing removes the lower bound.

## 3. Positive certificates for every balanced cut

Choose any subset S of peripheral coordinates with |S|=r; let T be its complement. Form two blocks:

    P_S = {s,y} union {v_j : j in S},
    Q_S = {v_j : j in T}.

Send v_T from Q_S to P_S (r bits), and send (y,v_S) from P_S to Q_S (r+1 bits). Both blocks can evaluate all their own next-state equations literally. The equations do not require the missing block's future state. These two local circuit equalities give an inductive implementation proof: at time zero the local records concatenate to the global state, and every update preserves that relation. This proves equality of all execution traces, without enumerating N*2^(N+1) states.

Thus every balanced S has an explicit persistent certificate under budget k=r+1. The witness stores S and the actual message-coordinate maps, not merely the message width or a task-output law. The family of candidate cuts has binomial(2r,r) members. This example does not assert that finding one is difficult: it provides a large boundary-forgetting witness family and a hard joint resource obstruction.

## 4. Crossing certificates need not admit an admissible joint refinement

Take S and its complement T. The two parent decompositions are

    ({s,y},v_S) | v_T,
    ({s,y},v_T) | v_S.

Their set-theoretic common refinement has blocks A={s,y}, B=v_S, C=v_T. Suppose its central incoming interface is a single message encoded from v, with at most k=r+1 bits, independently of s,y. Allow this encoder arbitrary preprocessing of all peripheral bits; this gives it at least as much power as separate B and C encoders.

**Theorem.** Every exact zero-error implementation for all admitted initial states needs an incoming alphabet at A with at least 2^(2r) messages, hence at least 2r bits.

**Proof.** If two distinct vectors v,w have the same message, choose an index j with v_j != w_j and choose initial selector s=j and the same y. The central decoder has the same own state and received message in the two cases, so must produce the same next y. The required next values v_j,w_j differ. Contradiction. Thus the encoder is injective. QED.

Since 2r>r+1, the intersection packaging violates the budget although both parent certificates satisfy it. The obstruction already arises on the first step, so giving the encoder arbitrary additional finite persistent memory initialized independently of the unknown selector does not remove it. No assertion is made for correlated initial encoder memory that already contains the receiver selector.

The witness failure is about an interface-bounded common refinement. There IS a common refinement with a 2r-bit input. It would be false to call this failure an unqualified nonexistence of any common refinement.

## 5. Boundary forgetting and fixed-endpoint recovery

A behavior-level view that retains the candidate whole and its task trace semantics, but erases the cut S and internal message-coordinate maps, sends all P_S|Q_S implementations to the same behavior. This is legitimate forgetting: the whole recurrence and task output y do not depend on how implementation state is packaged.

The positive certificate carries precisely the information erased by that view when an actual implementation is requested. Arbitrarily demanding the identity abstract refinement between two distinct specified cuts is impossible: an identity-shaped concrete refinement cannot move state coordinates between blocks. This is the dynamic analogue of the original C5 identity-forest obstruction.

**Scope warning.** This behavior erasure is a semantic map of the declared dynamic implementation doctrine. It is not, without an explicit typed embedding, a new substitution-congruence theorem for the original ordered-graph C5 profile. In particular message alphabets and state block types must be retained when assessing whether two operations are parallel. A claim that this example alone proves the original C5 kernel theorem would be wrong.

## 6. Timing and sensing qualifications

If the central component may first send s to the peripheral mechanism, then the peripheral can reply with v_s. The central input needs only one bit, while the outgoing request needs ceil(log2(2r)) bits, and there are two dependent communication phases. This removes the central input lower bound at the cost of changing the interface type and its latency.

Direct sensing of v_s by the central component similarly changes the allowed interface and removes the bound. A task that only needs an approximation or a restricted selector set also changes the required information. No claim about those variants is included in the exact theorem.

If the task permits an extra round of latency, a pipelined request/reply implementation may be useful, but its observable timing is not the original synchronous y'=v_s law. An explicit temporal abstraction would be needed to compare the two.

The example therefore tests whether the framework retains direction, timing, initial knowledge, and resource budgets in certificates. It is not evidence that the one-way contract is universally appropriate to robotics.

## 7. What would turn this into a discovery result

The admitted dynamic universe must be stated independently of the observations. Given finite readouts, a discovery certificate must include a member of that universe, its hidden-state trace alignment, a cut S, the local mechanisms, and the exact inductive implementation relation. Its conclusion is that this is a possible realization of those observations with the claimed task behavior. An actual-environment guarantee needs further identification or a guarantee uniform over the remaining models.

For this family, choosing S is not physical architecture identification. Nor do the readouts alone determine the recurrence. Those are limitations, not omitted proof steps. The family is suitable as a negative/positive implementation stress test accompanying a constructive general discovery theorem; it is insufficient as the entire validation of that theorem.
