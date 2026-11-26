# Scoped authority at the lift's effect window

[Exact issue law and limits](Effect_Window_Authority.tex).
An owner can authorize an old payload to remain onboard for a named trip.
The check concerns all possible effect cuts, not only request acceptance.

```sh
python3 -B window.py | cmp results.json -
```

`EffectWindow.lean` checked on AXLE `lean-4.35.0` with Mathlib;
two axiom audits, no `sorryAx`. This is a declared model,
not a qualified controller or physical lift assurance.
