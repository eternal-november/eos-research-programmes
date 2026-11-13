# Environment correlation determines causal controller capability

## Operational meaning and two parameters

An environment first announces a target block of zones. A tagged sensor stream reports every zone's binary route/interlock status. The environment then confirms the SAME block and specifies one zone within it. The controller must select that zone's safe branch. The target announcement, sensor values and final within-block selection are adversarial, subject only to the stated persistent-block promise.

Let there be m blocks of r zones, with N=mr total status bits. Complete input words are

    Start(j), Read(1,x1), ..., Read(N,xN), End(j,ell),

where j∈{1,...,m}, ell∈{1,...,r}, and x∈{0,1}^N. The required final response is x_(j,ell), meaning x_((j−1)r+ell). The first announcement does NOT reveal ell. The repeated block is an environmental correlation, not information secretly stored in the controller.

The controller is one deterministic finite-state register with b possible values and ONE time-homogeneous update table. Start/Read/End and the actual sensor identifier i are delivered tags. They are not inferred from a free internal clock. The resource model permits finite combinational decoding of these tags and unrestricted finite update/output tables. It bounds persistent register cardinality, not gate count, input bandwidth or every hardware cost. Output is produced only on End; no future readout is available early.

This is an exact task-demand model, not empirical robot certification. It assumes the status bit determines the safe branch, readouts/tags are reliable and the target block does not silently change. The theorem below contrasts this environment with one in which that promise is absent, without changing the task or the controller's physical input/output interface.

## 1 Every separate cut is cheap

At an individual cut, a hypothetical encoder sees the FULL observed prefix and a hypothetical later decoder sees the FULL remaining suffix. This is the per-cut criterion of Operational_Cut_Capability. It does not require that the encoding can be reached from the previous cut by a physical update.

**Proposition 1.** The maximum, over all cuts, of the minimum number of cut messages is exactly 2^r.

Proof. Before End, prefixes with different initial blocks have disjoint possible remaining suffixes: those suffixes contain End(j,ell), whose block must match Start. They never conflict in the cut confusability graph. Within a fixed block, encode the status bits of that block that have already been read, with zeros in not-yet-read positions. At most 2^r codes suffice. If the final requested bit has not yet been read, the remaining suffix supplies it; otherwise the code supplies it. At the cut after the complete sensor stream, all 2^r selected-block vectors are pairwise distinguishable by a suitable End(j,ell), so 2^r is necessary. After End, only the requested response bit matters. QED.

For r=1, every cut separately uses at most one bit, independent of m=N. The initial cut and the cut immediately after Start need one code; every later cut needs two. This does not imply a one-bit causal controller.

## 2 Lower bound for ONE causal controller

**Theorem 2.** Every deterministic b-state controller solving the stable-block environment satisfies

    b ≥ 2^[r ceil(m/b)],
    hence b ≥ 2^r and N ≤ b floor(log2 b).

Proof. After Start(j), the m target blocks occupy at most b memory states. Some state is reached for a set I of at least ceil(m/b) target blocks. Fix every status bit outside those blocks, and vary the r|I| bits inside them. For every j∈I the controller starts the SAME tagged sensor stream in the SAME memory state. Its memory just before End is therefore a function of the stream and that memory state, not of the particular initial j∈I.

If two different selected-block bit vectors led to the same pre-End memory, choose a differing bit, in block i∈I at offset ell. Append the SAME End(i,ell) to both. Both are admitted episodes because i lies in the initial-code class. Determinism gives the same response, but the demanded bits differ. Contradiction. The pre-End register distinguishes all 2^[r|I|] vectors, proving the exponential bound. Since I is nonempty, b≥2^r. Taking logarithms and using r ceil(m/b)≥N/b gives N≤b log2 b; integrality of bit-vector size gives the displayed weaker integer bound. QED.

The integer bound N≤b floor(log2 b) is necessary, not an exact finite optimum formula. The sharper first inequality retains the block grouping.

## 3 One-table construction and the capability law

Group the m target blocks into batches of k consecutive blocks, so one batch contains at most rk status bits. Use register values

- WAIT(g), for the ceil(m/k) batches;
- ACTIVE(v), a bit word of capacity rk;
- DONE(v), a completed batch bit word, padded if the final batch is shorter;
- a reset marker and, if responses are latched rather than emitted on End, two terminal response markers.

On Start(j), enter WAIT(batch(j)); the block's position inside its batch is deliberately forgotten. On Read(i,bit), waiting batches other than the currently scanned one remain waiting. At the selected batch's first position, begin recording. ACTIVE appends the delivered bit at the position determined by the actual tag i and becomes DONE after that batch's last position. DONE remains unchanged. The tag i identifies the current batch and within-batch position, so ACTIVE does not store a hidden phase counter or its original batch index. At End(j,ell), recompute the target's batch offset from the delivered j and ell and emit the corresponding bit of DONE(v).

One fixed table implements these rules on every input. Unreachable combinations may be completed arbitrarily. Forgetting the batch after recording is valid because End names a block in the SAME batch as the initial block, not because the controller guessed its value.

This construction uses at most

    ceil(m/k) + 2^(rk+1) + 3

register values. The count deliberately overestimates active partial words and includes explicit reset/output storage.

**Theorem 3 Uniform capability law.** For N=mr≥2, the minimum fixed-register cardinality is

    Θ(max(2^r, N/log2 N)),

with universal multiplicative constants independent of m and r. Equivalently, the required persistent memory bits are

    max(r, log2 N − log2 log2 N) + O(1).

Proof. The lower bound 2^r is Theorem 2. From N≤b log b, either b≥N, which already dominates N/log N, or log b≤log N, giving b≥N/log N.

For the upper bound let L=log2 N. If r≥L/2, choose k=1. Then ceil(m/k)=N/r≤2N/L, and the memory bound is at most 2N/L+2^(r+1)+3, which is a constant times max(2^r,N/L). If r<L/2, choose k=floor(L/(2r)). Then k≥1, rk≤L/2 and rk≥L/4. Consequently ceil(m/k)≤4N/L+1 and 2^(rk+1)≤2sqrt(N). For N≥16, sqrt(N)≤N/L, so the construction is at most 6N/L+4. The finitely many smaller N are absorbed into a universal constant. QED.

For r=1 this gives Θ(N/log N) register states, or log N−log log N+O(1) bits, although EVERY individual cut admits one bit. For large r the intrinsic need to retain an entire selected block dominates. This is a two-parameter law, not an exact formula for the minimum at every small integer pair.

## 4 The same partial descriptions admit radically different whole environments

Now change only the environmental promise. Let the final block k be independent of the initial block j:

    Start(j), Read(1,x1), ..., Read(N,xN), End(k,ell).

Keep the SAME task: answer the status of the zone requested at End, namely x_(k,ell). Keep the SAME tagged interface and controller architecture.

**Theorem 4 Lost matching changes capability exponentially.** This changed-block environment needs exactly 2^N register states, whereas the stable-block environment has the capability law of Theorem 3.

Proof. Fix any initial Start(j). Before End, every N-bit status vector must occupy a different memory state: if x and x' collide, choose a coordinate where they differ and issue the corresponding End(k,ell). Both episodes are now admitted, so the same state/input would have to yield two different answers. Hence b≥2^N. Conversely store the N-bit vector, using each Read tag to update its indexed bit, and use End to select the requested bit. Start resets the vector. A fixed table with 2^N states suffices; output can be emitted on End or latched by reusing two of those states. QED.

Crucially, the two worlds have exactly the SAME two local chart images:

    left chart: (initial block j, full status vector x),
    right chart: (full status vector x, final block k, final offset ell).

Both images are full in both environments. Their difference is the retained cross-chart matching j=k, not a local state absent from either chart. A reconstruction that joins these charts only on x creates the changed-block environment. Thus marginal description equality does not determine controller appropriateness.

### Actual typed interface comparison

Let X={0,1}^N. The left carrier is U=[m]×X; the right carrier is V=X×[m]×[r]. Over the fine boundary B=X×[m], use legs

    U→B: (j,x)↦(x,j),
    V→B: (x,k,ell)↦(x,k).

Their compatible product is exactly the stable-block record set. Coarsen the boundary by q:B→X, q(x,j)=x. The new compatible product is exactly the changed-block record set. The old product embeds into it, but the newly admitted mismatched-target records have no fine lift. Both component carriers are unchanged. Coarsening a description does not physically change a stable environment. If this larger compatible product is used as the uncertainty model for the same actual stable environment, the extra records can instead cause a false rejection of a controller that is appropriate under the retained promise. The comparison separates two genuine environment semantics and explains why the partial charts alone cannot choose between them.

For a dynamic original-Calc instance, attach the SAME finite input-phase chain to these latent carriers and advance it one step per actual tagged readout. Source and target maps preserve the latent carrier. Left-chart observations reveal the initial block and the status stream; right-chart observations reveal the status stream and the final block/offset. The other announcement is hidden in each chart. The fine and coarsened boundary graphs retain the common phase chain and status vector, and the fine one additionally matches the block value. Coordinate maps preserve phases and actual events. The combined physical observation reads the appropriate announced field at its specified phase, never the full latent vector in advance. The compatible-tuple maps are therefore actual graph-span witnesses; the stream-order semantics is the separate staged interface, not a reinterpretation of spatial substitution as time concatenation.

The completed-world graph can be exponentially large, as the parameterized proof explicitly acknowledges. The result is not an efficient empirical world-learning algorithm. Its point is a sharp semantic and capability distinction that the two partial charts alone do not determine.

## 5 Significance and baselines

There is ONE selected block, ONE shared sensor stream, ONE persistent matching promise and ONE physical controller. The lower bound depends on several initial target blocks becoming indistinguishable in the same controller memory, and on the obligation to answer after the same subsequent stream. This is not tensor padding by independent small controllers.

The very correlation that makes separate cuts look cheap creates the causal difficulty: an imaginary cut decoder can rely on the future repeated block, but a real bounded controller cannot use that future announcement while deciding what to retain now. Losing that correlation entirely makes the demands larger still, despite identical local chart images.

The quantitative engine is established communication/streaming indistinguishability, closely related to two-round INDEX tradeoffs. The grouping upper bound is likewise a familiar communication-space tradeoff, not claimed as a new mechanism. A primary comparison is Chakrabarti et al.'s discussion of the relevant INDEX tradeoffs and prior Miltersen et al. results: https://www.cs.dartmouth.edu/~ac/Pubs/random11augidx.pdf . What is established here for the dossier is the explicit environment family, all-cut capability calculation, one shared-table implementation, and the exponential effect of its actual typed interface-matching loss. The general reconstruction theorem must still explain how these demands are preserved or fail under the program's witnessed operations.
