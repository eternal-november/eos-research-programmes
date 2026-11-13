# Independent finite verification

The independently implemented `verify_beacon.py` enumerates Boolean port assignments rather than copying reported output tables. It uses explicit `require` checks raising `RuntimeError`; Python optimization cannot delete these checks. Current successful run: **3,443 checks**. `verification.json` records deterministic results.

## What was checked

* Every primitive board truth-table row; complement interface span and its inverse.
* All four combinations of adapter placement on the two distinct board occurrences. All retain four operational runs. Only Q-only adaptation has one fixed-mode mission witness, at mode zero; P-only passes signal at mode one but fails eligibility. Adapting both fails.
* Complete local records, their internal compatible tuples, physical and functional nested block witnesses, and both inverse equations for flattening/splitting. Physical block sizes are 4 and 4, functional block sizes 2 and 8, and all assembled whole relations have four records. No intermediate n or p is discarded by these maps.
* Explicit labelled reindexing between physical and functional partitions, with inverse and whole-record comparison square. Their frontier lists differ, and a positionwise second-coordinate identification is not even typed (P versus S). This does **not** verify an I4 planar rotation: none is claimed.
* Literal sequential spans with carry wires. Original physical apices have sizes 4 and 4; original functional apices 4 and 16. The five-node repaired physical apices have sizes 4 and 4; repaired functional apices 4 and 32. Each pullback has four records, with full flatten/restrict inverse maps.
* Opening the repaired Qminus module retains the unique intermediate j. Nested physical assembly of X with (Qminus,S), including the (J,Q) refinement, recovers the full seven-coordinate run. The same-whole repaired comparisons are distinguished from replacement of the old whole.
* Explicit repaired G5 Theta membership, both roundtrips and the full-record root square. Actual contextual atomic span paths are checked at every prefix, including the proper X,Y,Cbar,Dbar,Qminus,Y5,C5,D5 stages and whole physical/functional paths. Intermediate stage valuations need not extend to an admissible mission; they are checked independently.
* An old-to-new comparison over identity external endpoints cannot preserve the root square: at input (1,0), old output is (0,1), repaired output is (1,1).
* Local tables for N,P,S are literally unchanged by Q repair. No nonexistent old global mission certificate is transported.
* Mission quantifiers are fixed-mode then both alarm inputs, represented by (g,t0,t1), not per-input choices. Local certificate pullback exactly classifies these mission witnesses in this particular relay model.
* Mode-forgetting in the **atomic local mission-certificate diagram** yields the empty-to-singleton comparison. This is not a claim that hardware lacks executions, nor that forgetting mode at any arbitrary macro seam gives a spurious mission success.
* All four Boolean-valued observations of the two modes: constants lose the shared constraint; the two injections retain it and support the local good predicates. The analytic minimality statement concerns the declared local-predicate language. It does not concern only the constantly false original whole mission query, or smallest physical realization.

## Relation to machinery

The bijections establish the concrete singleton-fibre/exact-assembly conditions using complete retained witnesses, not mere agreement of final outputs. They may instantiate the coefficient-exact assembly criterion in the cited E5 framework once the report supplies its declared spans and cut data. The checker makes no claim that these multi-piece assemblies are opcartesian. The crossing-coordinate bridge is an elementary additional finite proof, not an admitted planar cut operation. The direct image/pullback ghost is not, without further matching, a direct instance of the differently oriented contravariant restriction theorem.

## Boundaries

This is exhaustive for the specified finite, deterministic, Boolean model. It is not physical validation of a salvaged beacon, a stationarity inference from bench observations, RF or timing analysis, redundancy/fault-tolerance evidence, a new general discovery algorithm, or a novelty result. Natural join/CSP reasoning independently accounts for the finite compatibility verdicts. The decomposition contribution tested here is retention and transport of named local witnesses, interfaces, cuts and occurrence-specific changes.

The code complements the analytic inverse-map proofs; it does not formalize them for arbitrary systems. No Lean claim is made.

## Replay

`python verify_beacon.py` and `python -O verify_beacon.py` should produce identical JSON. `source_only_replay.json` records a fresh temporary-directory replay containing only this source file, with source and result SHA-256 hashes. No installed research package is required.
