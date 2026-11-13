# Independent bounded cluster-quotient verification

Source alignment: `partition_quotient_candidate.md`, §§1–5, as read 2026-10-31. These are reproducible executable checks, not a proof of all degrees or a declaration that F1/F3 is accepted.

Run with ordinary Python 3 (not `-O`); each program has an explicit assertion-enabled guard. JSON output is deterministic and excludes elapsed time.

```
python verify_cluster.py > verify_cluster_results.json
python verify_cluster_formula.py > verify_cluster_formula_results.json
python verify_cluster_rewrites.py > verify_cluster_rewrites_results.json
```

## Main model

All ordered contiguous-clique graph types through four vertices, including the empty graph, are enumerated as compositions. All actual ordered partitions in degrees 0–4 are functions from labelled vertices to occurrence indices; empty occurrences are permitted. The group is explicitly the product of symmetric groups of the original clique intervals. Actual orbit SETS are compared with full matrix fibres, not merely representative hashes.

The main verifier checks hereditary type/restriction and identity-outside extension; all simplicial-map comparisons with actual restricted/grouped partitions; composition of every pair of monotone maps with all three degrees at most four; representative independence of actual nested partitions with outer and total inner degree at most four; exhaustive cut/flatten factor bijections for every interval including empty, unary, full and degree-zero boundaries; and fixed-coarse-representative active lift counts versus multinomials. The intermediate graph is recomputed from positive selected row sums; rows are never merged.

Category coordinates are factorized from graph coordinates. The nonthin category is C2 × [1], with two parallel arrows for each comparable endpoint pair and xor composition. Interval collapse checks retain actual arrow endpoints. The supplemental check explicitly counts composable paths in degrees 0–4 and verifies these are NOT the unrestricted Cartesian product of all arrows. This is not a claim that arbitrary independent arrows compose.

## Supplemental direct formula/heterogeneous fixture

`verify_cluster_formula.py` loads definitions only from the main verifier. It independently computes the candidate's row-reinsertion/concatenation substitution formula and compares it against 161,910 actual nested partitions. It checks all 800 matrix orbit fibres in degree four for the six-vertex cluster (3,2,1), and 56,000 monotone-map comparisons on representatives. An explicit deletion control retains two separate singleton rows when an intervening clique disappears.

## Genuine bounded rewriting, not morphism coherence

`verify_cluster_rewrites.py` constructs actual binary cut-labelled trees, evaluates their original labelled partitions, and executes literal R, L, UL and UR steps, including contextual steps. Initial trees have at most four binary leaf positions and at most four vertices; every eligible empty leaf may independently be a nullary unit. Descendants are included. Grades in this separate rewrite test are terminal. It checks semantic preservation and joining of every enumerated immediate local peak by explicit normalization.

PASS: 35,621 trees; 68,883 local peaks, of which 28,704 involve L; 16,603 L steps, 34,060 R steps, 14,029 UL steps and 14,029 UR steps; 1,805 semantic normal forms.

This does NOT establish completeness of critical-overlap template enumeration, the decoration rules, nonterminal-grade rewrite typing, or B3 ordinary/mixed O_L/MOut/MIn path coherence. In particular unique object normal forms do not by themselves prove equality of presentation morphisms. Those remain mathematical/source-audit obligations even when every bounded check passes.

## Scope boundaries

The candidate's all-degree proofs are separate from these finite enumerations. This is not the original F2 all-ordered-graphs C certificate, not a verification of arbitrary graph partition erasure, not the old scalar-terminal theorem, and not a replacement for an independently specified F3 target/morphism comparison. Both retained wholes K2 and K1 disjoint-union K1 have the same singleton input profile, providing the basic multivalued-output control.
