# 02 — Preservation, observational equivalence, and the cost of quotienting

**Origin:** the user's open-system target at chat L1958–1960, plus the original claims about boundary contracts at L2543–2589. **Status:** added formal design note; not a theorem asserted by the source.

## Define the consumer before defining equivalence

Let \(\mathcal K\) be the class of external contexts that may use a component, and \(\mathrm{Obs}\) the allowed external observations (including error reports, timing, termination, and resource use **if those matter**). A stringent notion of contextual equivalence is

\[
C\approx_{\mathcal K,\mathrm{Obs}}D
\quad\Longleftrightarrow\quad
\forall K\in\mathcal K:\ \mathrm{Obs}(K[C])=\mathrm{Obs}(K[D]).
\]

This cannot be evaluated until \(K[C]\) is given a composition semantics and the observable behaviors are defined. For refinement, replace equality by an explicitly oriented preorder. If a specification guarantees only absence of bad *finite traces*, trace inclusion may support refinement; it does **not** alone preserve termination, liveness, or progress under all contexts.

### Two kernels that must not be conflated

**Representational quotient:** an abstraction \(\alpha:S\to\widehat S\) identifies internal states. It may preserve a predicate yet fail to preserve enabledness, future behavior, or policy information. The abstract transition must be defined and checked separately, for example through simulation or bisimulation conditions.

**Observational quotient:** two implementations are indistinguishable for the chosen consumers and contexts. It can be coarser than state equivalence or stricter than equality of one-step input/output relations when feedback and failure are observable.

The relevant law is the stakeholder's verification/control contract, not an unconditional preference for the smallest state space. The gain from coarse models is reduced analysis cost; the hazard is deletion of a distinction that matters to a downstream consumer.

## Counterexample: a hidden cut that changes executable action

Let \(S=\{s_0,s_1\}\), with the same readout \(r(s_0)=r(s_1)=o\). A command \(a\) is enabled only in \(s_0\). Merging the two states is legitimate for the instantaneous readout, but not for a deterministic Boolean `enabled?(o)` or guaranteed safe execution. The quotient requires a *may/must* distinction or a belief state.

## Contract refinement is asymmetric

Suppose a server originally accepts commands in \(D\subseteq U\), and a replacement accepts \(D'\supseteq D\) with equivalent results for old commands. For a client restricted to \(D\), the enlarged domain can be a valid improvement. Requiring equality of restriction domains would reject it unnecessarily. Conversely, a replacement can preserve all successful output values but introduce divergence, violating a termination guarantee.

**Ratchet:** test two candidate implementations in every *allowed* interconnection—not in every imaginable universe. If the contexts include feedback, include closed loops; if they include clocks, include deadlines; if they include control, include the permissible observation histories and strategy classes.

**Related notes:** [09](09-observation-and-modal-affordances.md), [11](11-feedback-and-trace.md), [20](20-architecture-and-proof-obligations.md).
