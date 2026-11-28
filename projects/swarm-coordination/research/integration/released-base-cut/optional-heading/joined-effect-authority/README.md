# Common effect-cut admission from native VDA and RMF

The complete archive contains all exact source and Eigen files. For Git, materialize SOURCE.tsv inputs by basename in pinned/, RMF.tsv file paths under rmf/, and supply a C++20 compiler and compatible Eigen 3 include directory.

```sh
set -e -o pipefail
python3 -B replay.py [path/to/eigen3] | cmp - NATIVE.txt
python3 -B compare.py | cmp - RESULT.json
```

The argument is optional in the full archive. Rows give old VDA completion tick, witnessed physical exit tick, whether the grant retires at tick two, latest start, whether retirement is after observation, control mode, actual attempted start (0 if none), effect-law validity, and the hex-digit trace encoded as a decimal integer. Each cut encodes four bits: C callback, sampled range, effect range, witnessed clearance. Predicate checks are not physical motion.
