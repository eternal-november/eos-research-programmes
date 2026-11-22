# Repository guidance

Organize developments by mathematical subject, not temporary contract-obligation labels. Keep manuscripts, executable checks, and formal packages together with their required dependencies.

Keep the root README a short entry point. Do not add authorship, import provenance, workflow history, Library identifiers, or storage metadata to READMEs. Use Git history and commit messages for archaeology. Preserve mathematical hypotheses, scope limits, literature references, and reproducibility instructions.

Distinguish written proofs, finite diagnostics, historical formal-check evidence, and fresh proof-assistant verification. Never turn an import into a new certification claim.

## Result findability

Make substantive results discoverable by the question they answer. When adding, revising, or moving a result, update the project's canonical result index or navigation file and keep that entry point linked from the project README. Use one canonical index rather than duplicating parallel lists. Give each result a stable name or ID, a short searchable description, the hypotheses that govern reuse, and direct links to the relevant statements, proofs, and checks.

For cited repository notes in release manuscripts, provide paired [PDF, TeX] links to the same revision and identify the relevant theorem, section, or source anchor. For Lean, name the declaration and link to its source; state what formal verification has actually been recorded. For an executable example, link the checker and give its invocation and what it checks. Keep these kinds of evidence separate.

A manuscript may point to a proof or example elsewhere. If a rewrite moves or removes one, preserve a direct route from the claim or result index to the authoritative replacement. Before handing off a changed result, try a plain-language query without the theorem name or file path: the reader should be able to find the result, recover its scope, and tell which evidence supports it. A working link alone does not test that.

Maintain the external Library-to-repository comparison record for each import. Keep Library backups available for agents that cannot access this repository. Do not put that external storage bookkeeping in the repository.
