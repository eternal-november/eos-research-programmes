# Semantic scope and native debit after late authority
Run `python3 -B late_grant.py --source path --warehouse path --support path | cmp - LATE_GRANT_FINAL.txt`.
The pin sets and source parameters are the same as in the native authority
parent. In the standalone archive defaults are sufficient. The four arms
are scope receiver, direct scope receiver, last arrived, and upstream
presend rejection under explicitly additional authority.
