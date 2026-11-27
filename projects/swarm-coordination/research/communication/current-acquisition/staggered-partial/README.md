# Staggered partial acquisition and shared bias

Read Staggered_Partial_Acquisition.tex for the named current witness,
the exact two-sample bound, a linear-time amplitude threshold, and the
scope. The original platform callback is unchanged. The ADC, clocks, sign
interleaving and calibration laws are simulated controls.

Materialize the two pinned Git blobs in SOURCE.tsv under up/. Columns:
destination, repository, commit, source path, Git blob SHA. Requires
NumPy and SciPy; Python 3.12.14 and SciPy 1.17.0 were used.

    sh run.sh up | cmp expected.txt -

The source classifier uses successful per-channel evidence. The
ordinary controller still consumes its original published vector. No
deployment or acceptance claim follows.
