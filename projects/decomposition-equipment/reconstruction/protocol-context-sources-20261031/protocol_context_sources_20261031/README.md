# Protocol-context substitution and coherent reconstruction

31 October 2026. This is the reproducible source bundle for the scoped protocol-context reconstruction checkpoint. It is not a claim of generic novelty or a complete general theory of gluing, feedback or contracts.

## Reading order

1. `protocol_context_substitution_theorem.md`: explicit normalized token-context substitution, private-state conditional sufficiency, reconstruction at every finite-tree cut, actual path maps and same-cylinder canonical comparison coherence.
2. `polling_envelope_progress_theorem.md`: the separate uniform polling-envelope product/weakening calculus and its ordered-lock progress consequence.
3. `proof_review.txt`: clean mathematical review of the exact final sources and a bounded account of the executable evidence.
4. `prior_art.md`: primary-source context and the exact scope of the claim.

## Reproduce the finite checks

Use Python 3.10 or newer. No third-party packages are required.

```sh
cd protocol_context_sources_20261031
sha256sum -c SHA256SUMS
python3 -m py_compile verify_protocol_contexts.py
python3 verify_protocol_contexts.py > replay_stdout.json
cmp replay_stdout.json verification_results.json
cmp replay_stdout.json verification.log
```

The verifier writes `verification_results.json` and `verification.log` in its own directory, and prints the same JSON to standard output. The shipped copies are the exact final run output. For a stronger comparison, preserve the shipped outputs before running, or perform the replay in a fresh extracted copy. A valid replay has status `PASS`, 116,635 assertions, and the source/verifier hashes recorded in the JSON. The assertion count includes many path/window checks; it is not a count of independent theorem instances. Finite checks corroborate the proofs, not replace them. The CFS construction is not implemented, and the tail fixture is the deterministic zero-bad-event special case, not a stochastic P/G test.

`SHA256SUMS` covers every shipped file other than itself. Archive entries are a strict source allowlist; no executable environment, private transfer metadata or raw review history is required to reproduce the checks.

## Included dependencies

`dependencies/concurrent_progress/` contains byte-exact copies of:

- `ordered_lock_progress_theorem.md`: the previous intrinsic-service P/G theorem under an implemented cyclic scheduler. Its proof and assumptions are restated there; the new companion replaces the cyclic service constant by its derived hierarchical bound.
- `composition_challenge.md`: the earlier constructive fixed-context controlled-prefix bridge and its information-loss/correlation boundaries. This is an established dependency, not the protocol-context working review with a similar filename.

`dependencies/cylinder_audit/` contains byte-exact mathematical infrastructure notes:

- `isbell_external_product.md`
- `general_adequate_cfs_span_criterion.md`
- `isbell_comparison_span_coherence.md`
- `mixed_context_wiring_interchange.md`
- `compact_boundary_cfs_wiring.md`
- `traced_isbell_completion.md`
- `partial_trace_cfs_completion.md`

These record the earlier comparison-span, source-changing normalization and related completion results. Their stronger gluing/trace hypotheses are not silently imposed on the protocol language, and their completion results do not give its formal apices an operational implementation. References to other illustrative examples in those notes are background, not additional premises of the present theorem. The earlier excursion note is unnecessary for this bundle: the included concurrent theorem states and proves the reused P/G bound.

## Scope that must remain visible

- Countable states and records, finite context trees, at most one ultimate worker call per root tick; the identity adds no tick.
- Primitive pending records retain incoming state/input/branch. Exterior private information is retained only up to the pre-response boundary.
- Node-level logs are from the canonical expanded tree, not recoverable from arbitrary equivalent flattened kernels.
- Reconstruction/coherence is for one unchanged outer cylinder and its actual cut maps; genuinely different networks are not identified.
- Polling products and monotone weakening belong to this concrete certificate calculus. Deadlock/starvation remain permitted semantics.
- Resource progress requires one authoritative manager and the stated lock/intrinsic-service hypotheses. Root ticks are an abstract cost model, not hardware-overhead bounds.
- No arbitrary Isbell operad action, universal contract calculus, empirical identification or novelty claim is made.
