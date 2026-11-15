# Directed state feedback with coherent pure actions

[The theorem](Directed_State_Extension_of_Concurrent_Pure_Actions.tex) integrates retained state closure with directed sequential/parallel interchange. It continues the [directed state construction](../directed-state-and-relative-parallel/README.md) rather than supplying another concrete process model.

## Independent input and derived structure

The input is a process bicategory with coherent pure left/right actions and compatible directed parallel structure. These data are not inferred from an arbitrary relative pseudomonad. A stated sufficient pure-strand condition derives centrality from invertible pure restrictions of the directed compositor; it does not invert general effectful interchange.

The construction derives:

- sequential state composition and its coherence, preserving chronological effect order;
- a faithful native inclusion and inherited directed parallel compositor;
- typed tightening, vanishing, joining, strength and directed outer-state sliding;
- explicit independent sequential/parallel closure assembly maps and a four-process compatibility square (FC), retaining all four state factors and using the forward compositor.

The inclusion is **faithful, not generally full**. It preserves original native distinctions, but completion may add comparisons between their images.

## State reuse is not independent state allocation

Closing two processes separately retains two state copies. Closing their sequential body once reuses one state. The theorem does not equate these. A separate finite-state cardinality/flip-read test makes this boundary explicit; it is not a premise of the general proof.

## What remains open

This is structured-state feedback with the specified coherent input. It is not a free-feedback universal property, an instantaneous trace or yanking theorem, a theorem of arbitrary shared-interface admission, or completion of the broader feedback/concurrency programme. Compatibility of a particular relative presentation with the required pure/parallel input remains an obligation when applying the result.

The prior [geometric parallel criterion](../geometric-parallel-crossing/README.md) constructs part of that input under its own hypotheses. This package does not silently identify the assumptions of the two theorems.

## Literature and verification

Paquet–Saville's Freyd/action correspondence and concurrent pseudomonads supply the architectural precedents. The paper distinguishes those established results from the directed-state extension proved here. No novelty claim is made.

Independent written-proof review checked the action-based coherence, native slides, pure restrictions, inherited compositor, feedback law types and the explicit square (FC). Only pure structural comparisons and state-isomorphism slides are inverted. These are not mechanized proofs; TeX compilation was not requested or run.

```
sha256sum -c MANIFEST.sha256
```
