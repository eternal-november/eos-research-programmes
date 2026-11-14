# Constructive local fairness and controlled native completion

[Self-contained TeX manuscript](Constructive_Local_Fairness_and_Native_Completion.tex), continuing [information and progress](../information-and-progress/README.md).

This tranche constructs the admitted almost-sure fairness premise used by the preceding native progress theorem.

## Results

- Positive firing probability conditional on the actual full past gives almost-sure strong fairness; temporal independence is unnecessary.
- Legal independent private attempts plus an actual joint lone-acceptance guarantee give a concrete collision-tolerant realization.
- The joint next-state/event kernel square, matching observers and delayed controller connect that policy to native fair completion and a reflected receipt.
- An exact finite support criterion synthesizes safe stationary local policies with uniform positive task hazards. Local supports must form legal joint rectangles.
- Environmental timing changes the quantifiers: a response chosen before hidden current draws requires every response to admit some successful supported action; an action-observing response requires a supported action successful against every response.
- Uniform policies on passing supports give an explicit positive bound from the finite transition table.

## Scope

Almost-sure fairness is not fairness of every raw path. These criteria do not classify all history-dependent fair policies, guarantee deterministic latency, or tolerate an unconstrained hostile environment. Joint acceptance, local information, actual action legality, observer matching and completion effects must be modeled. The controlled completion theorem is conditional on the actual joint kernel, not merely equal separate marginals.

No historical novelty, Lean formalization or TeX compilation is claimed. The probability foundation is a standard conditional Borel–Cantelli argument, credited in the manuscript. Independent written review and exact finite diagnostics are not infinite-path proof certificates.

## Checks

Run from this directory:

    python3 checks/check_support_hazards.py
    python3 checks/check_conditional_hazards.py
    sha256sum -c MANIFEST.sha256
