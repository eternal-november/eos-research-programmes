# Tag design for reserve decisions

Read [the result](Tag_Design_For_Reserve_Decisions.tex).

```sh
set -o pipefail
python -B replay.py | cmp result.txt -
```

The replay checks all 1,094 nonempty labeled graphs through five
vertices against 54,178 tag partitions and 16,902 clock partitions.
For the 37 tag instances through three vertices, it also constructs
actual observation sets directly on the fixed-margin lattice.
The graphs are development instances, not observations from a plant.

For two modes, the prefix-extrema clock algorithm is compared with
all available cut positions on 1,024 signed inputs.
