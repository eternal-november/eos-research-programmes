# Exact finite marked-span certificate checker

Given two finite normalized rational raw-row tables and a **supplied typed relation** of legal candidate/reference pairs, construct or verify the local marked-span certificate from Section 6 of [Law and Possibility Repair for Dependent Protocols](https://github.com/eternal-november/eos-research-programmes/blob/f458186590df968a516ba73a8eb76fcf044544b0/projects/contextual-composition/protocols/law-and-possibility/Law_and_Possibility_Repair_for_Dependent_Protocols.tex#L657). Python 3.9+, standard library only.

```sh
python3 marked_span.py examples/covered.json > certificate.json
python3 marked_span.py examples/covered.json --verify certificate.json
python3 marked_span.py examples/coverage_failure.json
python3 marked_span.py examples/mass_failure.json
python3 -B -m unittest -v
```

Input fields are `candidate`, `reference`, and `allowed`. Each row has a side-local unique string `id`, a nonnegative rational `mass`, and a vector `cost` of nonnegative rationals. All costs have the same dimension (possibly zero), and each table has total mass one. Use JSON integers or strings such as `"3/4"`; JSON floats are rejected. The relation consists of pairs of row IDs. Supply the pairs allowed by the actual typed outcome relation. This checker independently enforces the coordinatewise cost condition on those pairs, but does not compute tree/leaf compatibility or infer missing pairs from cost alone. Keep duplicate raw witnesses as distinct IDs, even if their outcomes coincide.

Success returns a raw span with exact marginals, candidate-surjective projection, and reference-exact cost on every span row. The algorithm scales masses to integers, runs bipartite max-flow, and removes positive support cycles. It then retains one zero filler per zero-weight candidate row, even if its only partner is a zero-weight reference row. The witness has at most `|P| + |Q_positive| - 1` rows. Unmatched zero-weight reference rows are permitted. Ties are resolved by an implementation ordering, not a canonical span theorem.

Rejection may identify uncovered candidate rows, a deficient coupling cut, or both. The deficient-cut certificate lists a candidate subset, its complete neighbor set and their two exact masses; strict excess of candidate mass proves infeasibility. Verification recomputes the witness equations or verifies the stated failure proof without solving the flow again. Construction exits 0 on success, 1 on a mathematical rejection, and 2 on invalid input; verification exits 0 for either kind of valid certificate and 1 for a well-formed but invalid certificate.

The three fixtures are schematic raw examples, not a parser or executable interpretation of the dependent protocol language. The checker does not establish contextual closure, certify any unspecified input relation, or bound the expansion of dependent contexts. Max-flow and transportation support sparsification are ordinary algorithms used to construct the manuscript’s local certificate, not separate novelty claims.
