Safety zoning and coherent discovery lifting proof sources

Purpose and main result

This checkpoint develops two separate tests for a declared finite model. The
continuation-interface theorem identifies the least information needed to decide
all generated permission predicates. The generated-profile fullness theorem
checks whether every specified coarse decomposition witness lifts uniquely to
the original records, coherently through every finite generated refinement.

The thermal example applies both tests to one owner of heat and cooling charge.
Retaining heat and charge passes both tests; forgetting charge invents route
witnesses and loses exact task permissions. A duplicate regime label can be
omitted at the boundary because the component types already retain it.

Scope

These are mathematical proof manuscripts with finite executable regression and
independent-model checks. They are not Lean-formalized proofs, a complete solution
to an unrestricted decomposition theory, or an empirical robot safety
certificate. The general results assume finite carriers, the stated typed
grammar and retained component records. Controller observation, universal action
admission, adverse outcomes and task completion have their own stated
hypotheses. A witness-lifting obstruction rejects that specified witness; it
does not by itself establish that every route is impossible or a region unsafe.

Read the thermal example first for motivation, then the two theory notes.
FILE_GUIDE.txt describes every included item. AI_REVIEW_PROVENANCE.txt explains
what the review and executable checks do and do not establish.

Reproduce the checks

Use Python 3.10 or later, with the standard library only. This checkpoint was
tested with Python 3.12 and 3.13 on Linux. From the extracted folder run:


The runner verifies SHA256SUMS and the exact declared file set, checks the
source-provenance hashes, confirms that Python assertions are active, and runs
all four checker scripts in a fresh temporary copy. It compares every captured
stdout byte to its included expected output. It uses a fixed hash seed, forces
UTF-8/LF output, and removes inherited Python optimization settings. It refuses to run under -O,
-OO or PYTHONOPTIMIZE, rather than silently bypassing assert-based checks.
No installation or network access is required. The extracted sources are not
modified. Running a checker directly only prints its result; it does not update
the included expected-output file.

Successful completion ends with:

    PASS: all four checkers reproduced their expected outputs.

Hashes establish internal integrity, not authorship or a cryptographic signature.
The manifest intentionally does not hash itself. If files are deliberately
edited, keep an original copy and inspect the change rather than merely replacing
the expected outputs or hashes.

Prerequisite and external prior references

foundations/Original_Calculus_Dynamic_Interpretation.md is an exact copy of the
prior dynamic interpretation manuscript. Its original text and historical
references are preserved. The copy supplies the finite graph-operation model,
strict coarsening comparison and original occurrence-refinement interpretation
used by the current notes. SOURCE_PROVENANCE.json records its exact byte hash.

The prior note refers to material in its original checkpoint, not to additional
files hidden in this ZIP. In particular these remain external:

- Witnessed decompositions source and contract.zip, rooted at
  witnessed_decompositions, including the referenced original Lean modules;
- Exact_Dynamic_Factorization.md;
- Causal_Implementation_and_Control_Transfer.md;
- check_original_dynamic_bridge.py and the prior theory/original sources.

The earlier source archive and full prior proof bundle have not been duplicated
here. The prior manuscript's historical check counts are not rerun by this
checkpoint. The current runner executes only the four included checker scripts.
Exploratory notes, raw review/audit records, the early pre-entry fixture and later
formalization work are outside this curated checkpoint.

Verification scope: use the standalone mathematical checks identified in the project VERIFICATION.md. The original archive replay is not a supported repository command. No fresh Lean replay is claimed.
