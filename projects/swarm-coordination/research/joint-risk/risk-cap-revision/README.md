# Risk cap revision with an irrevocably committed reserve

[Model, theorem and bounds](Risk_Cap_Revision.tex) · [Exact replay](replay.py)

A later receipt cannot rescue a fast commitment when the new rule covers all outstanding physical exposure. The same implementation can be lawful under a grandfathering rule, but it then makes a different promise. Re-run the exact 1,152-case check:

```sh
sha256sum -c SHA256SUMS
python3 -B replay.py | cmp results.json
```

The bounded model uses the prior two-dispatch source and a stated synthetic hazard for one added dispatch. No compilation or physical validation is claimed.
