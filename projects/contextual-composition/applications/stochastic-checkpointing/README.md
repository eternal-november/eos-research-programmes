# Stochastic checkpointing

A basic worked example in the existing probability/list construction, not a new general theorem. It distinguishes preservation for a fixed initialization and weak observations from preservation with correlated references or arbitrary inputs.

- [Worked note](Stochastic_Checkpointing.tex): finite model, exact laws, native grade-map comparison and scope limits.
- [Exact checks](check.py): Python 3 standard library only; run `python3 check.py` in this directory. Ten rational-arithmetic assertions check the finite laws and distances. These are diagnostics, not Lean certification.
- [Underlying construction](../../foundations/relative-construction/delivery/One_relative_construction_for_context_content_and_effects.tex): probability/list composition and telescope accumulation already established in the retained programme.

The weak output laws agree for the chosen sampler. A retained correlated reference distinguishes replay from fresh sampling with total variation distance 1/4. A general typed checkpoint rule stable under permitted surrounding contexts remains future work.
