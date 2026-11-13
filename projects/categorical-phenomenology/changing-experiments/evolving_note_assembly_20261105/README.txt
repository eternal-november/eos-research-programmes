Changing experiments and composing characterizations
Research source and intermediate archive, 5 November 2026

READ FIRST
Changing_experiments_and_composing_characterizations.tex is the complete,
self-contained manuscript. It requires no other files to read or eventually
compile. No TeX compiler was invoked for this integrated manuscript.

The note derives changes of native experiment doctrines and gives exact
criteria for state, concept and support preservation. It then treats the
independent categorical problem of composing experiments across an interface
change, with an integer-resource classification and an explicit response
bridge. Native weighted synchronization supplies an unbounded cost defect
and a primitive endpoint-preserving witness compiler. Established machinery
and previous project work are attributed rather than presented as new.

CONTENTS
parts/ contains the manuscript's source sections.
checkpoints/ preserves timestamped assembly drafts, including superseded text.
source_snapshots/ preserves the component investigations and three recovered
  preceding manuscripts. Some earlier working drafts contain statements
  corrected by the correction logs; the integrated manuscript is authoritative.
bibliography/ contains verified primary-source references, access-depth notes
  and the project comparison audit.
checks/ contains source integrity results and fresh computational replays.
assemble_note.py reconstructs the self-contained TeX from parts and frozen
  source snapshots; it also saves another timestamped checkpoint.
check_source.py checks environments, braces, labels, citations and selected
  source-integrity conditions without compiling.
reproduce_checks.py replays four finite regression suites in checks/replay/.
  It uses Python's standard library only, copies the checking scripts before
  running, and does not require an external service.
build_archive.py rebuilds the source archive and its SHA-256 file manifest.

REPRODUCTION
From this directory, with Python 3:
  python assemble_note.py
  python check_source.py
  python reproduce_checks.py

All finite replays passed. They are regression evidence, not proofs of the
universal theorems. The source contains the mathematical proofs. The separate
Lean file and log certify only the explicitly identified elementary
row-quotient fragment. No claim is made that the entire note is mechanized.

ARCHIVE INTEGRITY
MANIFEST_SHA256.json records each included file's hash (apart from the
manifest itself). Intermediate drafts are intentionally retained, including
the record of material corrections. Compilation logs in component research
folders, if present, concern those component drafts, not this integrated
uncompiled manuscript. No compiled PDF is delivered.
