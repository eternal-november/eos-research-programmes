# Constrained speculative sampling

A finite contextual-composition integration example, not a new general framework or speedup claim.

The main point: preserving a supplied next-token law does not make local legality masking equivalent to global conditioning on eventual success. The note proves the finite continuation-mass criterion and instantiates the acceptance/correction witness map.

Run `python3 check.py`. All arithmetic is exact. No dependencies beyond Python 3's standard library. No Lean replay.

Sources: the programme's independent interaction criterion and plural-semantics manuscript; standard speculative sampling from Leviathan, Kalman and Matias (ICML 2023). See the TeX bibliography. Novelty is not claimed.
