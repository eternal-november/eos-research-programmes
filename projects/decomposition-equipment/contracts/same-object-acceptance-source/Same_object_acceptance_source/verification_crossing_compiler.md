# Executable normalized certificate compiler and exact loop ledger

31 October 2026. `compile_crossing_certificate.py` is an actual finite compiler/checker for a normalized special case of the bridge schema. It complements, rather than replaces, the theorem's general charged-input ledger. No old 8192 constant is assumed.

## Result

**PASS:** both destination charts for n=2,4,6,8,16,32; eight independently mutated invalid inputs rejected. Each accepted compilation takes exactly **445n+597 explicit word-RAM operations** in the program's accounting. The all-n count below follows by expansion of fixed loops, not interpolation or finite tests. JSON and console artifacts are `verification_crossing_compiler.json` and `verification_crossing_compiler.stdout.txt`.

```sh
python compile_crossing_certificate.py
```

## Required admission contract and excluded costs

The normalized input is a shape/type/range-validated `Input` with even n≥2, source/destination chart codes, four retained immutable references (original evidence, physical uncertainty K, confidence event, validated premise package), representative source IDs 0..n, n padded three-row triple bases, one padded two-row endpoint basis, six physical/primitive guard flags, numeric capacities/timing and a budget ledger.

The original evidence reference must **already validate that the supplied basis rows are exactly the sampled spans**, with physical capture maps and provenance/count/confidence obligations attached. The normalizer must bind canonical capture IDs injectively to the original `(port,time,event)` captures and verify that every probe/evidence map uses those same captures; assigning fresh canonical labels to an aliased or misbound raw capture is invalid. Permitted aliases would require a different declared schema. The core checks those normalized bases and their composite relation; it does not read raw samples or prove that a purported evidence reference is genuine. Similarly, a true guard flag denotes a supplied verified physical premise, not a premise established by a Boolean comparison. A standalone call with invented references is not a physical mission certificate.

`C_norm` pays parsing, type/shape/range validation, canonicalization, and validation of the injective map from original physical capture/resource names to canonical record IDs. `C_phys` pays validation of original evidence/provenance references and physical-premise/capability payloads (or their already verified dependency references). They may be split into finer terms. These are actual supplied time envelopes, not constants derived by this program. Both are added to the opportunity check. Arbitrary long identifiers, dH capture coordinates, sorting/deduplication, hashing, original sample verification, and arbitrary-precision rational calculations are not swallowed into the linear core bound.

One RAM word must accommodate every normalized input and every intermediate result, including 6n, 445n+597 and the complete time/cost product and sum. This includes values on rejected-input paths, not only accepted certificates. The admission layer must validate all these intermediate bounds and nonnegative range constraints, or a bit-machine must replace each word instruction by its proved bit-cost. Header fields are loaded into ten virtual input registers, charged once; repeated Python attribute syntax denotes access to those cached registers. No variable-width object hashing/equality is billed as one operation.

Compiler workspace is a **separate required admission check**, not covered by `caps[0]` (which checks only physical sensor storage). On the specified flat word-array layout, a conservative reservation is `32(n+16)` words: normalized input including nested-array headers is at most `8n+64`; all core arrays/output, even retaining all eight five-word template arrays rather than reclaiming them, are at most `9n+80`; at most 128 scalar/register words suffice. Their sum `17n+272` is below the reservation. These are abstract layout bounds, not Python heap measurements. The validated capability/premise package must establish this compiler workspace capacity and preserve physical storage separately; its checking belongs to `C_phys`. If a different parser/object layout is deployed, its actual storage envelope replaces this bound.

## What the core checks and emits

1. Source/destination chart codes, even n, source IDs, canonical occurrence references. Physical occurrence IDs are r_i=i, z_i=n+i and d=2n+1; the external normalization map retains their original meaning. Representative source IDs are a separate namespace.
2. Every triple span equals the full XOR plane (mask 105); endpoint span equals the diagonal (mask 9). Bases are padded with zeros. There are no data-dependent exponential searches.
3. The constant local source/delivery/XOR/seam template on all eight boundary/source assignments.
4. Explicit per-update cell records `[source ID, z occurrence ID, previous r ID, next r ID, source owner, XOR owner]`. Chart IDs determine the two crossing owner assignments. Occurrence IDs determine indexed grouping/reconstruction; concatenation of row-owner output lists is not the inverse.
5. A checked telescoping residual over 2n+2 coordinates: r0, every zi and d occur once; intermediate registers cancel.
6. Supplied stationarity/isolation/sensing/XOR/clock/interlock flags, n+1 capture capacity, one-bit column or two-bit row channel capacity, selected-slot bound 2n+1, and service/tail bound containing that slot. This matches the declared physical-controller fixture, not the 7m+3 representative-sampler clock. The positive compiler fixtures select slot 2n+2, leaving one spare tick after gate readiness at 2n+1. Equality at the minimum slot is licensed only when the validated physical premise explicitly orders gate readiness before the load event at that boundary; otherwise an extra margin is required.
7. Complete affordability: `C_norm + C_phys + tau_word*(445n+597) + service <= remaining`.

Output retains source and destination chart IDs, all four references, source IDs, generated ownership records, checked residual, compilation bound and total required time. A changed input span, reference cross-link, source ID, guard, capacity, timing or budget can invalidate the output. No new statistical confidence allowance is created merely by compilation.

## Operation model and derivation

`RAM` executes and meters explicit constant-register writes, reads, writes, integer add/subtract/multiply, XOR/OR/AND/shift, comparisons, selection and rejection branches at one operation each. A list allocation of length q costs q+1 (allocation plus zero initialization). A counted loop of length q costs 2+3q for initialization, final failed comparison, and per-iteration comparison/increment/jump. Its body is charged separately. Quotient-by-two and fixed register moves are explicitly charged. Helper routines are statically inlined RAM macros; their result registers are aliased rather than copied on return. Named variables denote instruction destinations, immediate constants are instruction operands, and `RAM.literal` explicitly charges standalone constant-register initialization. Phase labels, Python frames, counter bookkeeping and the returned debug operation ledger belong to verifier instrumentation, not the physical compiler output. The output is a fixed-offset eight-field RAM record; Python dictionary syntax is only its executable wrapper, not arbitrary-key hashing charged as constant time. Array zeroing, loop control, six `vals` moves and output allocation/field writes are charged explicitly. Interpreter/Python runtime is not being equated to this abstract word machine; hardware must supply `tau_word` or a conservative interpreter overhead envelope.

| Phase | Exact operations | Derivation |
|---|---:|---|
| Header | 22 | Ten loads; fixed scalar/branch checks and index arithmetic. |
| Retained references | 27 | Five allocation/init operations; loop 14; eight reads/writes. |
| Source IDs | 8n+11 | Allocation n+2; fixed loop overhead 2; n+1 iterations each seven operations including loop overhead. |
| Triple and endpoint planes | 324n+125 | Each triple: 15 outer-loop/index/reference operations, 307 subset-mask operations, two mask-check operations. Constant endpoint and loop setup: 125. |
| Local template | 288 | Nested-loop overhead 56 plus eight bodies of 29. |
| Assembly | 64n+4 | Cell allocation and setup 6n+4; each update body/outer overhead 58. |
| Telescoping | 49n+45 | Residual allocation 2n+4; n triple updates 27n+2; endpoint toggles 16; expected-residual loop 20n+23. |
| Guards/capability | 53 | Six flag checks including loop overhead 38; capacity and timing 15. |
| Opportunity budget | 13 | Explicit reads, bound/product/sum arithmetic and comparison/branch. |
| Output | 9 | One record allocation and eight field writes. |
| **Sum** | **445n+597** | Add the displayed affine terms. |

For clarity, the three-row mask uses eight subsets. Each subset costs 38: outer-loop per-iteration overhead 3, explicit value-register zero write 1, inner-loop fixed overhead 2, three iterations of 10, and mask shift/OR 2. Including the mask-register zero write 1 and outer-loop fixed overhead 2 gives 307. The two-row endpoint mask analogously costs 115. Thus both mask initialization and every per-subset value reset are charged. The compiler evaluates both selector arguments at fixed cost and padded basis lengths are constant; thus successful path counts do not depend on bit values or chart choice. Rejections exit early and cannot exceed this bound on otherwise admitted shapes.

The finite replay checks these counts, but the displayed counted-loop derivation is what establishes the all-n formula for this explicit program. This is **not** a universal compiler bound, a measured physical latency, or verification of opaque original premises.
