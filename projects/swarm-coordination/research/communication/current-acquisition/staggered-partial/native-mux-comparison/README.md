# Differential ADC acquisition as a stronger non-radio comparator

Read Differential_Source_Frontier.tex for the exact ideal observation
counts and the pin, timing, quantization and sign limitations. The replay
executes the unmodified pinned Python driver against a register-level mock,
not hardware.

Materialize exact SOURCE.tsv blobs under up/. The columns are destination,
repository, commit, source file, and Git blob hash. Requires Python 3 with
typing_extensions and Git.

    sh run.sh up | cmp expected.json -
