# Archival receipt frontier versus named gaps

[Technical note](Archived_Receipt_Frontiers.tex).
Run after staging all sources named in SOURCE.tsv under INPUTS:

    sh run.sh INPUTS | cmp expected.json -

The Space archive includes the source inputs under up/. This uses
ordinary local SQLite files and the pinned native RWARE journal. No
real operator audits, hardware effect settlement, or independent
mission are claimed.
