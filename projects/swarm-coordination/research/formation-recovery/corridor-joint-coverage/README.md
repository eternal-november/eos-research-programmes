# Corridor sensing and radio recovery

[Model, joint feasibility and information cutoff](Corridor_Coverage_And_Connectivity.tex).

```sh
set -o pipefail
python -B replay.py | cmp result.txt -
```

The replay compares integer-potential feasibility with a separately
enumerated placement and loss-set oracle on 1,700 instances. It also
checks 80 two-world reveal-time cases against common-prefix enumeration.
The proof justifies the integral comparison and continuous interpolation.
