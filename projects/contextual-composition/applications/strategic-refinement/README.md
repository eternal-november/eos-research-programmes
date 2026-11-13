# Cost refinement and strategic replacement

A bounded worked integration example, not a new general open-game theorem.

`Strategic_Refinement.tex` supplies the model, proofs and limits. `check.py` runs exact integer/rational diagnostics with no third-party dependencies:

```sh
python3 check.py
```

It checks 1,259 assertions. No Lean certification is claimed.

The central distinction: lowering implementation cost via a native computation cell does not preserve strategic best responses. Common-mode savings preserve all best responses at a fully action-observable payoff interface; the oscillation of savings bounds regret inflation. Sequential local checks alone are insufficient because earlier choices select future saving opportunities.
