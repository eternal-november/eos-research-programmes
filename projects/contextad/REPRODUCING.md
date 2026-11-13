# Reproducing the source checks

Use Python 3 and a disposable checkout; several checks write result files. These are finite diagnostics and structural source checks, not proof-assistant certification or a fresh mathematical review.

From `projects/contextad`:

```sh
python foundations/finite-contextads/check_expected_outputs.py
python applications/build_casebook.py
python synthesis/check_integrated_source.py
```

The first command replays both finite-contextad suites and compares their complete output against the retained expectations. The second assembles the eleven casebook fragments in order. The third checks the integrated manuscript's TeX structure, internal references, bibliography and external theorem-label addresses against the current repository sources, then writes `synthesis/integrated_source_qa.json`.

The source checker reports the files it actually checked. It does not certify that they match an original archive, compile TeX, check mathematical proofs, or establish the novelty of a result. Run each development's other Python checks in its own directory; scripts named `check_tex_source.py` may require the manuscript filename as an argument.
