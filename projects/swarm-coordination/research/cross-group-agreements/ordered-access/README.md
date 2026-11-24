# Dock access and blocking coalitions

A matched change in access preserves the old berth job and its payoff but
changes whether two optional parties can legally block the agreement. With
monotone completion payoffs and fixed credit limits, an earliest-feasible
completion certificate is exact for this question, not for all deviations.

[Model, proof and comparison](Access_Windows_And_Blocking.tex)

From this directory:
```sh
sha256sum -c SHA256SUMS
python3 -B replay.py | cmp results.json
```
The replay checks a direct payoff enumeration and an independent event
execution of legal schedules. The result is a scoped civil simulation and a
one-cut coalitional stability proof, not a theory of coalition convergence.
