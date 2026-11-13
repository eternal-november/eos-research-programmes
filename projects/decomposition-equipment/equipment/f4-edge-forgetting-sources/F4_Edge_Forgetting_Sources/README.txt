F4 edge forgetting source bundle
31 October 2026

Start with F4_Edge_Forgetting_Closure.txt for the result, original obligation,
evidence, review verdicts, and limits. The bundle is portable; no external
Python packages, network access, workspace paths, or credentials are needed.

Contents

proof/F4_Edge_Forgetting_Theorem.md
  Complete all-degree proof for the designated original M=1 discrete typed
  cuts. Includes the separate homotopy-groupoid interpretation and both
  negative controls. The main source is not an ordinary refinement nerve.

sources/Original_Completion_Contract_v0.1_VERBATIM.md
  The unchanged full original contract. Its historical OPEN status is
  preserved, not silently rewritten by this submission.

sources/F4_Obligation_Map.md
  Clean clause-to-evidence map, numerical-bound distinction, dependency
  boundary, and source identities.

sources/C1_Model_Theorem.md
sources/Global_Cut_Repair.md
  Byte-for-byte dependency sources. C1 supplies concrete graph cuts, actual
  K-arrows, and restriction identities. CUT sections 1 to 4 supply the exact
  all-degree cuts and the original discrete slice. These sources retain their
  historical scope/status statements and references to their wider original
  source collections. Those wider collections are not bundled or accepted
  here; their unrelated results are not needed for the F4 proof.

evidence/verify_f4.py
evidence/verification_readme.md
evidence/results.json
evidence/run.log
  Standard-library finite verifier, precise factorized domain, and its
  published run. Graph and category coordinates are checked separately,
  not by enumerating their full Cartesian product.

review/F4_Scoped_Review.md
  Non-author automated review with separate correctness and original-F4
  scientific-scope verdicts, replay provenance, and assurance limitations.

MANIFEST.json
  SHA-256 digest and byte count for every payload file, including replay.py.
  The manifest cannot contain its own hash. The surrounding ZIP and report
  have separate SHA-256 entries in the accompanying delivery checksums.

Replay

1. Extract the ZIP into a new directory.
2. From the extracted source-bundle directory run:

     python3 replay.py

The script verifies the manifest, copies the finite checker to a temporary
directory, runs every bundled finite check, and compares the deterministic
result bytes exactly. It does not overwrite the supplied evidence.
It also confirms that optimized Python execution is rejected before results
can be produced. Do not run with -O: the verifier uses assertions as checks.
The recorded run took approximately a minute; hardware affects elapsed time.

A successful replay establishes exact bounded reproducibility, not the
all-degree theorem, all F2 triangulations, C3/F2 formal acceptance, F3/I3
completion, or whole-program acceptance. Read the proof and review for those
distinctions. This package deliberately stops at the original F4 task.
