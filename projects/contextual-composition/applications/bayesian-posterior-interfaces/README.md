# Bayesian neural posterior interfaces

Read [the manuscript](Bayesian_Neural_Posterior_Interfaces.tex). This finite worked example characterizes exactly when a linear posterior summary is closed under Bayesian evidence updates. Its minimal stable interface is the likelihood-generated algebra (posterior masses of observational parameter classes). A one-neuron family gives sharp, arbitrarily late failures of truncated predictive summaries.

Run `python3 checks.py` (standard library only). It writes `results.json`; exact rational computations, not a stored success fixture. No Lean or TeX compilation has been performed. Written proof is supplied; independently reviewed at the stated scope. No novelty or practical neural-training claim.

Catalogue coverage: Bayesian/stochastic neural systems (stochastic structure plus inference), not a complete stochastic contextad enrichment. This is distinct from the prior checkpointing and speculative-decoding examples: its main object is a reusable posterior interface with an exact closure criterion and horizon-dependent alternative.
