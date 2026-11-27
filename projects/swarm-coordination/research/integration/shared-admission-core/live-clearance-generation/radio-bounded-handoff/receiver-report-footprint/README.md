# Receiver headroom before and after the report about it

Read Receiver_Report_Footprint.tex for the guard and the refinement boundary.
Materialize the pinned blobs in SOURCE.tsv under up/. Columns are destination,
repository, commit, source path and Git blob hash. Requires Python 3, SQLite,
NumPy, NetworkX, GNU-compatible shell tools, Git and a C++17 compiler.

    sh run.sh up | cmp expected.json -

Case parameters are capacity, primary TX debit, main receiver debit, report
route (0 absent, 1 shared receiver, 2 distinct verifier), whether the certified
mode reserves report bytes, report size, and policy (0 post-read local view,
1 naive earlier view, 2 priced receipt, 3 fixed backup). The returned tuple
preserves pre and post receiver state separately from the supplier chosen,
actual old delivery, and optional service.

The replay checks 3,840 native broker parameter cases and 16 matching
warehouse station cases. Reselecting the old sender after a genuinely
missing or late certificate does not turn that absence into a qualified
physical observation.
