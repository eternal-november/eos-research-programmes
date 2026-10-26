# Stored initialization before bank participation

Status: derived initialization adapter with independent proof/record recheck. This is ordinary stored-program initialization applied to the required obligations, not a new recovery algorithm or a source admission. The existing recurring-control/RUNTIME was inspected: its mutable instruction image, elementary loads/stores/branches and retained-prefix semantics are reusable ideas; its aligned invocation and image-phase construction are not imported. The present result stops before useful information and full controller behavior.

## Typed state and reset boundary

Partition a cartridge's state into C (mutable stored instructions and static configuration/template), W (finite private working words), I (incoming observation-interface words), processor registers/program counter, and external queues/held physical effects. I is not a subset of W merely because an implementation might place both in one address space. The partition states causal write authority and which policy guarantee a fault can invalidate. Changing only an input frame leaves execution intact. A proposed implementation that permits the same input-only attack to bypass every corroborating path requires its own source result; the partition does not forbid that attack by renaming it.

The elementary reset law puts the instruction pointer at the declared entry address and disables ordinary asynchronous control transfers during the prefix. It does not change C, W, I or external effects. Register contents may initially be arbitrary. Any interrupt controller, DMA writer, debug port or peripheral capable of altering private W/PC during the prefix must be either physically isolated by the actual preparation contacts, represented in the admitted raw fault footprint, or retained as a failure of this adapter. Ordinary observation writes to I may continue arbitrarily. They are not treated as control-state faults and do not affect the proof because the prefix never consumes I.

Let W have Q>0 words of fixed width w with Q+1<2^w. The intended stored prefix is the following elementary program, followed by the actual maintenance/control suffix. The first three instructions initialize every register consumed by the loop. All addresses and branch targets have finite encodings.

```
0: r_addr := 0
1: r_zero := 0
2: r_limit := Q
3: W[r_addr] := r_zero
4: r_addr := r_addr + 1
5: if r_addr < r_limit then jump 3
6: jump main
```

These instructions reside in the same mutable C that was inspected/copied. No primitive instruction means clean, initialize, correct image or successful boot. In particular, a different C may jump directly to main or emit an effect. The nominal main program must not write C; that later preservation obligation is separate. An ordinary processor can still write C under malicious instructions where the source permits it. The bootstrap conclusion is conditional on actual prefix bytes remaining the intended bytes throughout this run, not on a claimed image hash or a cartridge name.

## Prefix proof and finite work

At entry to instruction3 with r_addr=k, the invariant is 0≤k<Q, r_zero=0, r_limit=Q and W[j]=0 for every j<k. Initialization establishes it at k=0 independently of all initial register/W/I values. The store establishes W[k]=0; addition yields k+1≤Q<2^w, so no word overflow occurs. The branch either returns with the invariant or exits with every W word zero. The final jump reaches main. Exactly3Q+4 instructions execute. No prefix instruction reads I, branches on initial W or emits an actuator command. There is therefore no initialized-value premise hidden in the loop.

If execution of each elementary instruction takes at most δ_exec of real powered time including its scheduling allowance, the prefix finishes by (3Q+4)δ_exec. This is an upper execution-time premise on ordinary hardware and the actual schedule. It does not apply during power loss, a halted/defective CPU, arbitrary-code execution, or unbounded preemption. A tighter batch-rate bound may be used after its actual scheduling proof; elapsed wall time cannot be replaced by instruction count without this relation.

The all-zero postcondition is a formation condition for the main suffix: its layout interprets zero as invalid cache, no selected candidate, cleared cursor/count and zero new requested force. If a field instead needs a nonzero value, the actual prefix must write that value or the suffix must establish it before use; names alone cannot reinterpret stale bytes as initialized. A finite layout/cost proof for the complete new controller remains open. This generic prefix does not establish that an illustrative8192-cell image already contains that controller.

The register postcondition is not all-zero: r_addr=Q, r_zero=0 and r_limit=Q at exit. Any additional register consumed by the suffix must be initialized before use or appear explicitly in its precondition. The zero guarantee applies to the declared W words, not arbitrary peripheral registers, stack modes or physical driver latches.

## Output, freshness and ready execution

Private initialization does not clear external outputs or cancel earlier packets. The new side's effecting contacts remain physically disconnected until a source-derived travel interval exceeds the actual prefix and old-command drainage bounds. New private output registers are cleared without clearing the old side's held outputs. The suffix then obtains required observations through INFORMATION's actual bounded-age/path mechanisms before entering the useful routine class. Let B_exec bound this prefix, B_evidence bound that actual availability and B_entry bound the applicable driver/response transition. A consumed readiness bound must cover their proved dependency order, conservatively B_exec+B_evidence+B_entry, rather than granting readiness at power-on.

In particular, this prefix emits nothing and therefore leaves the new side's own external held-command latches unchanged. Before reconnecting its maintenance drivers, the actual suffix must write neutral/current commands to their finite physical ports and wait through application and old-packet drainage, or an explicit physical reset law must establish the same effect. Clearing RAM and merely waiting do not reset a latch. Reordered old commands require a clearing command applied after their last possible arrival; the CONTINUITY/OPERATIONS2D+J discipline is a conditional way to supply that order. The keeper side's ports remain separate. A world-output port must have an actual0.6/informed service-preserving command applied before blending; a neutral zero is not credited as positive flow. These remain B_entry construction obligations in the cyclic source.

W's cleared validity flags are not evidence that I is empty, current or true. A late old packet may arrive immediately after main begins. The suffix must reject/handle it using the actual finite freshness construction. Caches/timers in a power-paused bank likewise cannot resume with unchanged validity unless their elapsed-age relation survives; unconditional boot invalidation is the proposed branch. A reset into the prefix must occur on each newly powered activation, not only at commissioning.

An effective fault during the prefix can invalidate the conclusion and remains in the same raw history. That failure does not license calling an intact executor's forged-input behavior Byzantine. The prefix isolates one narrower implication: with actual intended instructions, specified reset entry and no unaccounted private control writer, arbitrary initial private data and arbitrary incoming observations do not prevent finite initialization. Whole-primary-frame robustness belongs to the subsequent policy and evidence proof.

## Executable challenge boundary

bootstrap_model executes the seven elementary instructions, with arbitrary initial private words/registers and incoming-interface changes. It checks3240 three-valued private/register initializations for Q=1…4 and explicit Q=32,1024,8192 cases, verifies instruction count and unchanged C, and challenges missing reset entry, corrupted stored instructions, an unisolated late private writer, stale input, interrupted prefixes and retained external effects. The model's main marker is a proof-observation point, not a successful control opcode. Independent checking reproduced the record and the general prefix invariant. It also checked a material budget boundary: Q=8192 requires24580 instructions, so a proposed B_ready=16384 is insufficient at one quantum per instruction even before evidence acquisition. Faster demonstrated instruction service or a larger bound is required. No complete mission policy, physical isolation, evidence acquisition or recurrent field support is proved by this component.
