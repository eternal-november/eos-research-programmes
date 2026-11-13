# C2 local relation interface checkpoint

This additive checkpoint supplies a genuinely different model from graph cuts:
its components are binary relations on finite interface sets, and its operation
fibres separately express containment and equality of relational composition.
The whole is independently supplied. Thin semantic fibres do not equate raw
primitive labels or presentation trees.

Start with:

- `Results_Workstream_C2.txt` — results and final verification/acceptance boundary.
- `research/workstream_C2/C2_Targets.md` — unchanged pre-proof reviewed target.
- `research/workstream_C2/proof/C2_Model_Theorem.md` — uniform model, all-arity
  substitution/restrictions, incident-compatible maps, and public A correspondence.
- `research/workstream_C2/lean/RelationInterface.lean` — actual generic public
  containment/exact `Calc`, inclusion, A2 free extension, and restriction slice.
- `research/workstream_C2/lean/README.txt` — precise P/L/C and axiom boundaries.
- `research/workstream_C2/finite/DOMAIN.md` — exhaustive domains and named fixtures.
- `research/workstream_C2/review/` — non-author P/L/C review and independent tests.
- `research/workstream_C2/PriorTheory.md` — direct standard Rel baseline attribution.
- `research/workstream_C2/REPRODUCTION.md` — full inherited-plus-C2 source rerun.

The principal 2→3→2 example retains one realizing outer pair and loses another
under a non-surjective intermediate restriction. Its original exact cell remains
valid containment but becomes nonexact. A many-to-one surjection gives a positive
comparison without bijective realization tuples. Nullary composition is the
diagonal, whose pullback is a kernel pair: exactness there needs injectivity,
not vacuous surjectivity at nonexistent internal positions.

For the separate parent-appointed L/API review, run:

```
python3 research/workstream_C2/review/reproduce_formalization_review.py --output /tmp/c2-independent-review
```

Its independently authored harness additionally runs `BoundaryGuards.py` and
records its exact output alongside a fresh isolated seven-module A2 dependency
build, generic C2 source, independent axiom/probe checks, finite rerun and source
mutants. This supplements (rather than silently substitutes for) the aggregate
`bash verify_workstream_C2.sh` reproduction. See its CLI help for output options.
The core source snapshot covers the aggregate's frozen input files; the final
export manifest covers every archived file, including supplementary review code.

All 445 prior archive files remain unchanged. No existing acceptance ledger or
contract is rewritten. Full C2 remains OPEN until the required D2/E integration
is separately performed. No C3 or D/E phase is activated, and no novelty or full
equipment claim follows from this familiar model.
