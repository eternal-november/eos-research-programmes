# Controlled training quotient probe

The useful candidate is an exact discrete-versus-continuous observability theorem for two-layer matrix learners, with a scalar exception, fixed-width boundary, resource-rank consequence and sharp bounded-depth noise barrier. No historical novelty or new general universal property is claimed.

Files:
- gram_behavioral_theorem.md: precise setting, complete algebraic proofs and scope addenda.
- check_gram_behavior.py: runnable SymPy rational/symbolic checks. Run `python check_gram_behavior.py`.
- check_results.json: successful run, including 108 closure identities, 108 cubic difference checks, 96 finite recoveries, scalar/rank checks, symbolic witnesses and 30 stationary-target checks.
- prior_art_and_scope.md: primary-source comparison and explicit unresolved literature limitation.
- SHA256SUMS.txt: final file hashes excluding this manifest itself.

Main claim: with mn>1, arbitrary matrix-target simultaneous GD at known eta !=0 has full Gram behavioral quotient, revealed by all target words of length at most two. Controlled gradient flow only reveals the Gram data modulo (L,R)->(L+cI,R-cI). A strict fixed-width distinction exists exactly when h>=max(m,n); the scalar-scalar interface never has it. Exact full-output reset access is required for the supplied finite recovery procedure. These are exact-model claims, not empirical verification.

Latest checks passed 2026-11-05. Novelty remains unresolved; ordinary Gram quotients, complete-shell constructions, instantaneous metric ambiguity and discretization-sensitive observability have close or direct predecessors.
