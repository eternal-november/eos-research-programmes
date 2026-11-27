# Verify the continuation before rewriting a shared command

See Reserve_After_The_Write_Is_Too_Late.tex for the named effect model,
native cuts, scheduler grant, side-service cost, and the independent
writer-unavailability counterexample.

Materialize SOURCE.tsv under up/ using its exact Git blobs (destination,
repository, commit, source path, blob SHA). Use Python 3, SQLite,
Git, and a C++20 compiler:

    sh run.sh up | cmp expected.json -

This is an authored cooperative reservation linked to selected native
simulator bodies, not an assertion of stock runtime scheduling rights or
an actuation and safety experiment.
