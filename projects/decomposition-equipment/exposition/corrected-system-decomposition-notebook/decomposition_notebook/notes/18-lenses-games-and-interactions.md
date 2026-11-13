# 18 — Lenses, open games, and interaction semantics

**Origin:** chat L679–680, L825–844, L922–926. **Status:** corrected scope and added discriminating definitions.

The common intuition is **bidirectional or interactive composition**, but these constructions answer different problems.

## Lenses/optics: a typed forward/backward interface

One elementary lens shape is a pair

\[
\mathrm{get}:X\to Y,\qquad \mathrm{put}:X\times R\to S,
\]

viewed as a morphism \((X,S)\to(Y,R)\). For an ordinary lawful state-update lens, additional lens laws such as Get–Put and Put–Get may be required; the general optic/lens shape alone does **not** ensure they hold. A backward map is not by itself a causal controller, optimizer, derivative, or gradient. It transports a *specified backward type of information*.

## Open games: play, coplay, and equilibrium are distinct data

A standard set-based open game includes a strategy set \(\Sigma\), a forward play map \(P:\Sigma\times X\to Y\), a backward coplay map \(C:\Sigma\times X\times R\to S\), and a context-indexed best-response/equilibrium selector. In the compositional game literature, **open games are morphisms** in a suitable monoidal category; they are not generally “strategy profiles as morphisms.” The additional best-response data is essential; play/coplay alone do not define a game. See [Ghani–Hedges–Winschel–Zahn](https://strathprints.strath.ac.uk/64265/) and [Hedges, Morphisms of Open Games](https://www.sciencedirect.com/science/article/pii/S1571066118300884).

Nash equilibrium existence is a separate theorem or failure of a selected strategy class. In every finite normal-form game with nonempty finite actions there is a mixed equilibrium; pure equilibrium may be absent. Accordingly, “morphism with no Nash equilibrium” is not a generic categorical exception handler.

## Dialectica and witness/counter-witness decomposition

Dialectica-style constructions distinguish choices/witnesses from challenges or counter-witnesses. This can clarify adversarial specification and test design **when the game/logic translation is defined**. The mere presence of two players or a minimax objective does not establish a Dialectica category of dynamical systems, nor does it yield a synthesis algorithm automatically.

## Geometry of interaction (GoI)

GoI and related traced/interaction semantics can model feedback-style token or information flow. Their operational content depends on how the interaction machine, trace, and observation are interpreted. A diagrammatic loop is not automatically a physical feedback law or a convergent iterative controller.

## Selection rule

Use lenses when there are well-typed forward and backward information channels; open games when strategic evaluation and best responses under composition matter; Dialectica when construction and challenge are genuinely dual in the selected logic; GoI when the behavior of interaction through feedback is itself the modeled primitive.

**Related notes:** [11](11-feedback-and-trace.md), [20](20-architecture-and-proof-obligations.md).
