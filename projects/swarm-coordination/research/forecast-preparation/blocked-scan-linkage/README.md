# Coarse tagging of two-scan records

[Proof, model and decision criterion](Block_Tags_And_Forecast.tex).

```sh
set -o pipefail
python -B replay.py | cmp result.txt -
```

The replay enumerates 672,984 identity permutations for binary rosters
through size seven and checks 2,177 local count budgets. It compares
finite reachable sets with the separation criterion in 2,048 multiblock
cases and constructs the large pooled and tagged witnesses explicitly.
The guarantee is for a controller that sees counts, not true identity.
