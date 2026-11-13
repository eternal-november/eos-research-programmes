# Finite verification record

These are bounded computational checks of **derived counterexamples** in the notes. They do not establish the general mathematical existence/composition theorems in the architecture proposal.

## Observation descent criterion (Note 09)

For \(S=\{0,1,2\}\), \(O=\{0,1\}\), with \(r(0)=r(1)=0\) and \(r(2)=1\), all 64 partial endomaps \(f:S\rightharpoonup S\) were enumerated. For each, all 9 candidate partial maps \(\hat f:O\rightharpoonup O\) were enumerated. An exact descent \(\hat f\circ r=r\circ f\) existed **if and only if** domain saturation and output consistency held. Exactly 24 of the 64 internal maps admitted descent. The mathematical iff proof is in Note 09; this computation is a finite check.

## Relational domain obstruction (Note 08)

For \(R(0)=\{0,1\}\) and \(g(0)=2\) with \(g\) undefined at 1, with the candidate restriction defined by the identity relation on existential domains, the two sides of the restriction axiom are:

\[
\bar g\circ R=\{(0,0)\},\qquad
R\circ\overline{g\circ R}=\{(0,0),(0,1)\}.
\]

They differ, disproving the proposed restriction structure on this relational interpretation.

## Two external law operator flows (Note 04)

Take \(V=\partial_x\), \(W=x\partial_y\), from \((x,y)=(1,4)\), \(t=3\), \(s=2\). Applying the \(V\)-flow then \(W\)-flow gives \((4,12)\). The opposite order gives \((4,6)\); their second coordinates differ by \(st=6\).

## Instantaneous feedback (Note 11)

For \(u\in\{0,1\}\), the equation \(u=1-u\) has no solution; \(u=u\) has two solutions. Used in \(F(*,u)=(u,h(u))\), these produce respectively no fixed-point feedback solution and two distinct external outputs.

## Scope of checks

The more substantial construction claims—typing a restriction-aware open-system category, obtaining a compatible feedback trace, lifting actions through law changes, and proving an assume/guarantee assembly theorem—remain **unproved design obligations**. The finite checks are diagnostic witnesses, not certificates for those ambitions.
