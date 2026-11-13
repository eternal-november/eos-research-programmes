# Reproduce the C3 checkpoint

Contract v0.1 unchanged SHA256
`47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e`.
C3 target SHA256
`88ea710752d99cd83d10c85740f825b1c543d58c0f475615c667020bc1aa2825`.

Use the unchanged `lean-toolchain` (Lean 4.35.0) and `lake-manifest.json`
(mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`). Install the
pinned public dependencies with the normal Lake workflow. The local convenience
environment at `/workspace/shared/witnessed_B_20261024/toolchain_recovery/env.sh`
is not a portable requirement or an input theorem.

From a fresh extracted source tree, with `lean` and `lake` on PATH:

```
bash verify_workstream_C3.sh
```

The driver checks every one of the 578 inherited source/archive files against
its preserved hash, unchanged contract/target and C3 source snapshot; reruns
the COMPLETE inherited C2/C1/B/A chain; reruns author and separately implemented
C3 finite checkers and their executed negative controls; compares deterministic
certificates; and checks hashes again. Logs/result.json are written under a
new `reproduction_C3/<timestamp>/` directory, never over saved evidence.

The inherited scripts compile project Lean sources afresh and audit their
axioms/negative probes. Public pinned dependency objects are reused; Lean and
all mathlib are not bootstrapped from source. C3 adds P/X proofs and independent
C evidence, not new Lean assertions. A full inherited rebuild does not transform
the new all-size mathematical arguments into kernel proofs.

Standalone finite commands:

```
python3 research/workstream_C3/finite/check_c3.py --output /tmp/c3-author.json
python3 research/workstream_C3/review/IndependentFinite.py --root . --output /tmp/c3-independent.json
```

The independent checker also runs after copying only its source to a clean
directory, omitting `--root`; this verifies finite logic without importing
author code or project helpers. Its standalone output differs only in the
declared input-verification mode, not mathematical results. It still embeds
the frozen contract/target IDs as provenance, not as available local files.

Graph enumeration means all m=0..4, k=0..5; it never claims exhaustive coverage
of unbounded empty-block arities. Full-size/all-arity results are P. The typed
chain product argument, actual executed counts and represented product counts
are documented in `finite/DOMAIN.md` and the proof. The six-vertex anchored
family has 8192 graphs; the unrestricted theorem is not inferred from this
finite test. Relation matrices cover a=0..2, b=0..3 only.

Independent P and C reviews, source hashes and clean-run evidence are part of
the checkpoint. Mathematical/scoped acceptance belongs to the parent, not the
script. C1/C2 later integration gates and all unauthorized workstreams stay OPEN
or inactive. Agent-managed review is not external human certification.
