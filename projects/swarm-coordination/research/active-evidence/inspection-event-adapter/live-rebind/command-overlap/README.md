# A delivered rebind command can use its own fallback budget

Scope is the selected byte-pinned civil broker under a declared
early command cutoff. First old bytes 2, tail bytes 2, capacity 5,
early command at .4 and tail at .75. Retain actual sender/receiver
ledger identities, including aliased ones. The command's actual
received callback and the old tail are distinct.

An aliased one-byte command fits with the required tail. An aliased
two-byte command may arrive on time but leaves only one byte for
old work. Cancelling a still-queued optional send cannot undo the
command's incurred debit. A physically dedicated pair still pays
old plus the same two-byte command. A failed command may incur TX
while giving no causal permission to rebind. The control only
cancels optional when actual fallback is still feasible. An
unplanned shared command may perturb optional as well.

This is a check of a supplied authorized command schema and
native payload accounting, not a claim about compressing real
authorization or network overhead. It demonstrates where an
otherwise disjoint egress/relay argument would fail if its
resource assumptions were broadened. The exact direct byte
ledger ties over all 32 rows; no field or independent result.

Use SOURCE.tsv and the timed-source-producer directory at main
804f0cc9b1f38044e63be901a49bd945636334a3:

    sh replay.sh /path/to/upstream /path/to/timed-source-producer | cmp expected.json -
