# Byzantine Control Research Execution

## Task authorization and scope

The user explicitly authorizes subagents for this Byzantine-control research session and directs the coordinator to delegate related-work checking before substantial original research. This is the task-specific exception to earlier user-level instructions that prohibited delegation without explicit authorization. Do not request that authorization again.

For this task, the orchestration procedure in this document supplies the delegation, interference, and reintegration requirements in place of a separately installed generic-agent-orchestration skill. An unavailable generic skill is therefore not a missing prerequisite for executing this authorized protocol. This exception concerns the user's delegation instructions; it does not override higher-priority instructions, actual tool permissions, repository acceptance authority, or the protection of unrelated work.

Use subagents within the research session. This authorization does not request separate user-owned chats, recurring jobs, external communications, or work on other projects. The coordinator owns the overall formulation, allocation, integration, and final verification. Workers receive explicit scoped tasks; returned work is evidence to assess, not an automatically accepted result. Further delegation by a worker requires a coordinator assignment that carries the same scope and resource limits.

[HANDOFF.md](HANDOFF.md) defines the research target, R1–R8, mathematical safeguards, and artifact contract. This document governs execution, prior-art discovery, parallel work, and Git isolation. Read both before starting the research. The existing [verification record](VERIFICATION.md) describes the limited mathematical foundation already checked.

## Related work before substantial original work

Front-load a targeted literature investigation for each substantial theorem, construction, or novelty claim. The aim is to identify what is already established, which assumptions its results require, and what remains to be done for the chosen target. The frontier means the relevant boundary of current human knowledge; absence from the repository or from one search is not evidence that a problem is open.

Delegate the initial related-work checks to subagents. Prefer a small set of complementary searches organized around obligations that can change the first research choice. Adapt them to available agent slots, relevant source access, and the overlap already found.

Supply each researcher with a precise candidate statement or an explicit formulation uncertainty, the relevant context indices, the closest known sources, and the decision their findings should change. Ask them to look for existing solutions, stronger or weaker results, impossibility boundaries, alternative terminology, formal libraries, and explicit statements of open problems. Searching only for papers that support the proposed framing defeats the purpose.

The coordinator may clarify definitions, reproduce supplied checks, inspect primary algorithms, and construct small discriminating examples while searches proceed. Such work can be necessary to formulate a useful query. Delay large proof developments, elaborate architectures, and novelty claims for an obligation until its first related-work assessment has been integrated. The gate is per obligation; an unresolved institutional search need not stop a well-supported discrete-control attempt.

A useful search return identifies the exact result, primary source and version, relevant assumptions and conclusion, support actually inspected, and the translation or gap relative to the target. It also distinguishes an explicitly documented open problem from an apparently uncovered combination of assumptions. Record search terms, terminology variants, citation trails followed, relevant sources not accessible, and the boundary of the search. Bibliographic reality, theorem-statement checking, proof reconstruction, and application to the local model remain different verification states.

Apply a result-sensitive disposition. A result that already solves the target under compatible assumptions should be imported, reproduced where verification requires it, and used. A result with different assumptions creates a refinement problem. An impossibility result may reject the target or justify a specific changed context. An explicit open problem can support a frontier claim within its stated scope and currentness. A search that finds no solution supports a bounded negative finding and a candidate for investigation, not a claim of universal novelty.

The first substantial attempt is ready when the coordinator can state the closest verified result, the comparison of assumptions, the remaining obligation, and why the chosen work is more useful than importing or adapting that result. Where retrieval is inconclusive, preserve the uncertainty, state the bounded search coverage and the cost of proceeding, and avoid novelty claims. Search need not prove that every relevant publication has been found. Reopen the assessment when a definition changes, an unexpected obstruction appears, or a new result could alter the chosen attack.

Maintain one live frontier and prior-art assessment organized by research obligation. It should distinguish repository residuals, checked literature boundaries, documented open problems, and provisional gaps. Do not count several papers repeating the same upstream theorem as independent support. Keep a bounded follow-up search active when it can still change an expensive research decision. A stopped search should identify what would restart it.

Reconstruction of known mathematics can be valuable for formalization, testing an encoding, or establishing an interface. State that consumer before investing heavily. Reproving a standard result for its own sake or renaming an existing construction does not discharge the program's substantive research target.

## Isolate the research from the existing working tree

The primary checkout contains substantial unrelated uncommitted work. Preserve its files and staged state. Do not prepare it for the research by committing, stashing, resetting, cleaning, restoring, moving, or bulk-copying that work. Its dirtiness is not a defect the research session should repair.

Use a clean integration worktree for the research. Start it from an explicitly selected commit containing the complete current handoff and this execution protocol. Record the resolved commit SHA, absolute worktree path, and branch. A default remote branch may predate these instructions; verify the start commit instead of relying on the worktree tool's default. Prefer a `codex/byzantine-control-...` branch with a unique session suffix when a branch is needed. Inspect existing worktrees first and reuse one only after establishing its ownership, base, and suitability.

Git linked worktrees have separate working files, indexes, and HEADs but share repository objects and ordinary branch references. A commit-based checkout does not import the primary checkout's uncommitted edits. These properties make worktrees suitable here, but they do not create an operating-system sandbox. [Git worktree documentation, checked 2026-10-04](https://git-scm.com/docs/git-worktree).

Record the primary checkout's initial branch, HEAD, and dirty-path status without staging anything. This is a boundary record, not a request to archive the contents of other projects. Other users or sessions may subsequently change that checkout; do not revert their changes merely because they differ from the initial record. During the research, treat that checkout as read-only. Any separately authorized final integration into it is a later operation.

The new checkout deliberately contains only the selected committed state. If needed guidance or an input exists only as an uncommitted primary-checkout file, identify it specifically and read it there without moving or committing it. Do not copy the entire dirty checkout to obtain one dependency. Necessary claims can be independently reconstructed and verified in the research artifacts; preservation of another project's pending edits is not permission to import those edits into a research commit.

Creating a worktree does not necessarily change an agent's default working directory. Every worker must receive its actual absolute working directory and verify its repository root, branch, and base before writing. Prefer explicit `git -C` paths and explicit shell working-directory arguments. Derive source, proof, and output paths from the assigned checkout. Keep generated files and temporary build outputs inside that assigned workspace or its designated temporary directory. If tool permissions prevent use of the clean workspace, report the concrete limitation and continue read-only research; do not silently fall back to modifying the dirty checkout.

The research write scope is `theories-and-designs/byzantine-control/` in the assigned checkout, plus specifically assigned local build or temporary files. Reading another project does not authorize editing it. Shared repository configuration, root dependencies, global Git settings, other project files, and remote branches are outside this write scope unless separately authorized.

## Match isolation to the assignment

Related-work researchers and semantic reviewers should usually be read-only. They may share a committed research snapshot and return their findings through the subagent channel; the coordinator incorporates useful material into maintained artifacts. They do not stage, commit, switch branches, edit shared definitions, or run commands that rewrite project files. If a long report needs a file, the coordinator can write it or assign a private output location and one owner. Treat a worker writing a tracked report as a writing worker under the same isolation rules below.

Give each concurrent worker that edits research files its own branch and worktree, based on a recorded coordinator commit. The coordinator creates or assigns those workspaces. Workers commit only their own scoped changes there. Separate worktrees prevent shared-index interference; nonoverlapping file ownership and stable interfaces still reduce integration conflicts. Do not have two agents simultaneously mutate the same checkout's index or working files.

Where separate worker worktrees are unavailable, retain read-only parallel research and let the coordinator perform writes serially in the clean integration checkout. A worker can return a proposed patch or proof for the coordinator to apply. This is a capability-limited fallback, not a claim that same-directory subagents are automatically isolated. If subagent tools themselves are unavailable, disclose that limit and preserve the same prior-art and checking obligations in the work that can be performed.

A suitable initial allocation leaves the coordinator responsible for formulation and integration while a few researchers investigate the nearest results. Add implementation workers only when an obligation has a sufficiently stable interface and a useful acceptance test. More agents are not automatically better: shared unresolved definitions, duplicated searches, and expensive joins can erase the benefit. Keep one owner for the semantic core, one maintained claim ledger, and an explicit route for proposed changes to shared definitions.

## Delegation contract and reintegration

Before dispatch, instantiate the handoff boundary for that worker. State the obligation and intended decision or artifact, the relevant definitions and assumptions, the inputs it may rely on, its read and write scope, whether it may commit, the exact working directory and base commit, and the check that would make its result usable. Include the important exclusions and open alternatives. Specify task extent by concrete coverage or artifact size where useful, with a stopping condition and the residual to return when blocked.

Use hard constraints for actual boundaries: local-information restrictions, source support, protected files, ownership, Git authority, and the proposition being checked. Keep proposed methods and uncertain organizational choices revisable. Do not tell a worker that a guessed theorem, schema, or proof route is mandatory. If the research target itself is unsettled, ask for a comparison or discriminating result rather than a proof of the coordinator's favored formulation.

Choose the overlap between assignments deliberately. Two researchers can provide useful independent checks when they use distinct derivations, search routes, or implementations. Two summaries of the same unchecked paper do not become independent evidence. A verifier should receive the exact statement and relevant model, with enough independence to challenge the author's encoding and assumptions.

Workers return the result, its support, the assumptions it depends on, changed files and commit identifiers when applicable, commands actually run, failure or counterexample witnesses, and unresolved obligations. Literature returns include source passages or precise locators and honest checking status. A worker that cannot discharge its assigned obligation should name the missing condition and its effect instead of silently substituting an easier task.

The coordinator receives by refinement: check that the result addresses the assigned obligation under compatible assumptions, then integrate it. Recheck cheap facts and load-bearing source passages. For a formal result, inspect the theorem statement, encoding, and axiom dependencies, then rerun the relevant checks on the integrated version. For a counterexample, confirm that the allegedly violating behavior is admitted by the model and respects the adversary's information and capabilities.

When results disagree, retain the disagreement long enough to identify a source mismatch, different hypotheses, or a real obstruction. A majority of agreeing subagents is not a mathematical verifier. Shared-definition changes must be propagated to dependent work before those results are assembled. Local success cannot close the parent obligation while the compatibility proof is missing.

## Git ownership and integration

The coordinator owns the integration branch and its index. A writing worker owns only its assigned worktree branch and permitted files. Literature and review workers have no Git mutation authority. The coordinator alone integrates worker commits, changes shared branch arrangements, or retires worktrees.

Before any staging or commit, verify the absolute checkout root and active branch against the assignment. Inspect the complete diff and untracked files in that checkout. Stage explicit paths or reviewed hunks. Do not use repository-wide `git add .`, `git add -A`, or `git commit -a` as a convenience. A path allowlist alone is insufficient when a file already contains someone else's edits: determine ownership at the diff level. If unexpected staged changes appear, stop Git mutation and establish ownership; do not unstage or discard someone else's work to make the index convenient.

Inspect the staged file list and staged diff before committing. Each change must belong to the assignment and have the intended content and authority effect. Run the checks appropriate to that unit, including staged whitespace checks. Commit one coherent contribution with the repository's session-record discipline: purpose, result status, material semantic changes, verification, and live residuals. A commit records work; it does not accept a theory or elevate a conjecture.

Integrate into the clean coordinator checkout only. Review each worker's diff against its recorded base and account for prerequisites before cherry-picking or otherwise applying selected work. Avoid importing unrelated commits merely because they share a branch. Resolve conflicts by inspecting the competing meanings, not by blindly choosing one side. Repeat the affected proof and assembly checks after integration; a worker's previously passing build does not certify the combined result.

Keep the completed research on the integration branch with its checked artifacts and a clear resumption entry. Report the branch, commit, and worktree path. Do not automatically merge, rebase, or cherry-pick into the dirty primary checkout, and do not push remote changes unless separately authorized. The initial documentation update that establishes this protocol can be committed with explicit reviewed paths; it does not license the later research team to use the dirty checkout for its work.

Before removing a worker worktree, verify that needed commits are reachable from a retained branch or integrated history and that useful untracked or ignored artifacts have been preserved. Leave uncertain work recoverable. Use managed-worktree lifecycle tools when applicable; do not force-delete worktrees or rewrite shared branches as cleanup. Keep the final integration worktree available for review and continuation unless its removal is requested.

## Artifact organization

Organize by independent intellectual identity, reuse, and maintenance needs. Split a proof, theorem, model, literature assessment, or benchmark into its own artifact when another task needs to address or revise it independently. Keep tightly coupled definitions and arguments together when splitting would increase reconstruction cost. File boundaries need not follow agent assignments or disciplinary boundaries.

Retain one maintained home for each shared claim or definition and link other uses to it. Distinct hypotheses can justify distinct variants; apparent duplication is not enough to merge them. Give composition obligations an explicit location when several individually supported results still need an assembly argument. A short TODO should expose current obligations, dependencies, blockers, and reachable next steps; Git carries routine authoring history.

Begin with the smallest layout that supports the actual artifacts. A prior-art assessment, semantic model, theorem/proof files, reproducible benchmarks, and synthesis may warrant separate homes. Do not instantiate an expansive directory tree, metadata regime, or one-file-per-agent archive merely to resemble a mature project. The relevant principles are reproduced here; the repository's [layout guidance](../../../agent-docs/directory-layout-guidance/layout-as-presentation.md) provides further rationale, and its [directory example](../../../agent-docs/directory-layout-guidance/subproject-directory-layout-example.md) is illustrative rather than mandatory.

Maintain only enough live orchestration state to resume safely: active assignments and owners, shared-definition version, worktree paths and bases, incoming results, and pending compatibility checks. This may live in the local TODO or a small coordinator record. Once work is integrated, retain the intellectual result and meaningful residual; avoid a second permanent diary of agent activity.

## Closure checks

Before the final synthesis, confirm that the substantial original-work attempts were preceded by an adequate related-work assessment and that later discoveries were incorporated. Check that a verified existing result was imported when it already discharged the target, and that an unresolved search was not relabeled as a frontier theorem.

Confirm that every integrated contribution has a compatible context, a known owner, a reproducible check or an explicit residual, and a maintained artifact home. Review emergent failures across agents' boundaries: changed definitions, incompatible fault budgets, hidden centralized information, and gaps between certificates and realized effects. Distinguish mathematical proof, source checking, executable evidence, and independent semantic review in the final report.

Confirm the integration branch's diff contains only authorized research changes. Report any unexpected workspace or Git mutation without attempting to conceal or automatically undo concurrent work. Leave the unrelated uncommitted state in the primary checkout outside the research commits. Final delivery follows the research contract in [HANDOFF.md](HANDOFF.md), including the integrated result and a truthful resumption TODO.
