# Contextual Composition: Editorial Guidelines

*A companion to “Computation in Context” — Editorial standard, version 1.0*

## 1. Editorial objective

**Make the framework intelligible and impressive simultaneously.**

The central attraction is a reusable mathematics for describing and composing computations with changing requirements, produced effects, dependencies, shared interaction, and feedback. The individual technical results establish where that architecture works, how it can be reused, and where it fails. They are evidence for the story; they do not each need to become the motivating problem of a separate article.

The intended reader personas include:

- an engineer who is intelligent, short on time, and perhaps has a passing familiarity with basic category theory.
- a mathematical expert who wants to identify the mathematical connection and the actual increment over nearby or personal work quickly.

Before writing or revising the opening, model the intended reader's point of view: what they already know, what they care about, which problem or intellectual possibility they would recognize, how much attention they can spend, and what they can connect to their own work. This is a theory-of-mind obligation, not a request to flatter an imaginary audience. Do not assume the reader shares the author's research context or feels the importance of an internal proof question. Make the significance and the idea intelligible in the same passage; do not postpone the compelling part until after a dry primer.

Neither reader should need to know the internal development history, theorem names, contracts, or why a particular proof obligation was originally posed. Do not dump readers immediately into the weeds. A manuscript often needs to support to some degree two simultaneous reading paths, unless it is being intentionally made for one of the personas.

**Reader contract:** After ten seconds in the abstract, a nonexpert should be able to explain in everyday language why the general idea matters, without understanding its technical vocabulary. After two minutes, that reader should understand the core organizing distinction and one concrete kind of benefit. An expert should be able to locate the principal construction, its scope, nearest precedents, and technical contributions without following the entire narrative.

## 2. The governing idea

A useful orienting claim is:

> **Composing work combines their dependencies, not only their inputs and outputs.**

More verbosely:

> We know how to describe many kinds of computation: functions, parameterized programs, probabilistic processes, stateful systems, concurrent processes, and feedback loops. But real systems combine these features. The difficulty is not just representing each feature; it is making the representations work together without losing the information or guarantees that matter.\
> This research develops a common mathematical framework for such combinations. It makes explicit what a computation requires, what it produces, how those requirements change, and which relationships survive composition, interaction, and changes of representation.

A computation can require context, produce structured effects, change what future stages need, interact with shared state, or make further work possible. These aspects should be visible in the model and governed by rules for combination.

Build the public-facing explanation around that idea. Introduce context as what a computation depends on and content as what it produces beyond an ordinary result, while acknowledging that these are choices of presentation rather than an exclusive classification of all effects. Explain an interaction rule as the mechanism making independently specified ingredients compose. Then show how comparisons, concurrency, feedback, and abstraction fit into the broader programme.

**Do not turn “everything combines” into a slogan.** The construction has precise hypotheses; some combinations require further data or fail. Flexibility means a meaningful range of supported models and controlled changes of model, not unconditional compatibility.

## 3. Sell the work. Hit the audience over the head with intelligible motivations, not the repository's theorem inventory

### Opening script: a plain technical problem → real stakes → a concrete promise

**Open with the theoretical difficulty in one sentence that an ordinary reader can understand without decoding the nouns.** “Knowing how each part works does not always tell us what will happen when we connect them” is a usable beginning. “Independently modeled systems,” “changing what other systems can do,” “context,” and “coherent relative interaction” are not usable first-sentence explanations. A specialist can receive the precise formal version immediately afterward. The opening's first job is to communicate an intelligible problem, not to compress the theorem statement into English.

**Next, make its consequences impossible to miss.** Give one or two credible cases in which that type of difficulty mattered, naming what went wrong, who suffered, and what it cost. Numbers, deaths, shutdowns, lost production, or irreversible physical damage are stakes; abstract nouns such as “reliability” and “coordination” are not. Use a documented incident rather than an exotic toy problem engineered to fit the theorem. Correctly label estimates, observed losses, affected populations, and time horizons.

**Then promise a payoff the manuscript can deliver.** Explain in everyday language what the mathematics supplies: for instance, rules for building a description of a whole from descriptions of its parts, while retaining the dependencies and shared effects that matter. Point to the actual construction, comparison theorem, or substantive realization that fulfills the promise. Distinguish the broad research ambition from what has already been proved, without interrupting the opening with a catalogue of caveats.

**Illustrative opening (two paragraphs):**

> In engineered systems, locally correct components can combine into an incorrect whole, producing **hidden incompatibilities, cascading failures, and catastrophic losses**. For example, in October 2025, a bug in Amazon's automated management of service addresses spread across AWS services, causing an outage that cost U.S. businesses an estimated **$500 million–$650 million** ([Parametrix](https://www.parametrixinsurance.com/reports-white-papers/aws-us-east-1-outage---what-parametrix-monitored-in-real-time)). Similar challenges arise in power grids, factories, security, robotics, transportation, and scientific experiments, where resources are shared and actions cannot always be undone.
>
> **This research develops a general mathematical framework for understanding how complex systems fit together and behave when they interact.** Building on established theories of computation, resources, effects, and dependencies, we develop novel constructions for combining them while preserving the information needed to establish system-level guarantees. The aim is to make such reasoning reusable across different systems, even as their components and relationships change.

The [AWS post-event explanation](https://aws.amazon.com/message/101925/) documents the incident; the cited Parametrix figure is a modeled estimate of losses to U.S. businesses, not an audited revenue total. This opening establishes recognizable stakes and states a broad mathematical ambition. It does not claim that the research has been shown to prevent that outage or automatically certify arbitrary engineered systems. The manuscript must later identify the constructions and hypotheses that substantiate its promises. The scope extends beyond software reliability.

**Opening audit:** Read the first sentence to a nonexpert. Can they explain it using familiar things? If not, replace the abstract words rather than adding definitions in parentheses. After the incident, can they identify the human, economic, scientific, or physical consequence? After the promise, can they say what the work will *give* them, without relying on “framework,” “composition,” or “coherence”? If the opening communicates only the size of the disaster, or only a technical theorem, it has failed. Both the stakes and the mathematical contribution must be intelligible, with the latter supported later in the paper.

\
TODO:

- the issue with leading by examples is that, while the framework is very general, most examples are so complex and rarefied that they tend to feel like one is presenting a solution looking for a problem. Some examples avoid this; e.g. discussing how to prevent an AWS outage during an update/change caused by independently developed interacting components
- When you lead with an example, qualify that the framework is yet much more general. With the AWS example, remind that the mathematics can do a lot more than facilitate reliability. When the project is first present, the framing should usually couple application-level salience with framework-level generality
- computer systems in particular enjoy properties that make them well behaved; such assumptions often simplify the engineering, making the applications of the project harder to see in that domain. But there are a ton of applications in other engineering disciplines.



Opening motivation should use a recognizable intellectual situation: components are useful because they can be assembled, yet assembly changes which assumptions and dependencies matter. It should not begin with an obscure mathematical obstacle or a highly specialized synthetic example and imply that the audience has long been waiting for its solution.

Use the three-beat opening order above: one short statement of the general technical problem, one or two consequential examples, and a clear promise that the body will fulfill. Introduce the detailed formal machinery afterward. State one grand promise per article and give the article a memorable identity; subordinate results should support that promise.

**Manufactured-problem test:** Remove the paper's most unusual example. If the introduction no longer gives a compelling reason to read the work, its motivation has been built backward from a proof.

**Trivial-baseline test:** If an elementary existing method already answers the advertised question at the same interface, say so; explain what the framework additionally organizes, preserves, or transports. Do not claim categorical necessity merely because a category-theoretic representation is available.

## 4. Preserve the distinction between framework, realization, and application

The writing should separate three different evidential levels.

The **categorical framework** supplies structures, hypotheses, constructions, comparison maps, and coherence results. A **realization** interprets them in a particular computational doctrine, such as finite stochastic histories or recurrent arenas, and may support significant theorems of its own. An **application** instantiates a realization with a model, protocol, or system-specific judgment.

An important theorem at one level does not automatically establish a theorem at another. Native maps in a constructed category are not physical capabilities. A normalization law is not a liveness proof. A finite example is not a proof for arbitrary contexts. An operational interpretation is not evidence that all possible context/content presentations have been unified.

Use explicit claim statuses: established background; proved here under named hypotheses; previously proved in a companion source; proved for a selected realization; demonstrated by finite computation; conditional extension; open.

Cite primary sources at the exact point where their hypotheses matter. Written proof, mechanized proof, historical replay, source checking, and numerical diagnostics must remain different evidence types.

## 5. When a design-space approach is appropriate, make it explanatory

Use a design-space approach when it helps readers understand the paper's subject or contribution; it is **not mandatory for every manuscript**. When used, the design space must be **explanatory at a minimum**: show the meaningful choices, what each enables or changes, and how the choices fit together. Make the generative and compositional relationships intelligible, rather than relying only on a list of named constructions.

A design space should help readers understand consequential choices: what interfaces count as pure, how context and content are represented, what resource and grade maps are available, which information is shared, which interaction or feedback operations are admitted, and what observations a comparison must preserve.

For each major choice, explain **what changes**, **what composition requires**, and **what comparison or theorem is available**. Where useful, show how changing one choice affects the admissibility or meaning of another.

Taxonomic, classificatory, encyclopedic, and observational presentations are **optional additions**, not approaches to avoid. A catalogue, comparison table, or classification theorem may help readers navigate the alternatives or may itself be a substantive contribution. When a design-space approach is used, such material may supplement its explanatory core rather than replace it. Para, Kleisli, spans, cospans, logical doctrines, and tracing may be useful points of comparison; naming them alone does not explain how their structures relate or prove that one unrestricted construction implements them all.

Do not describe axes as independent if changing one changes another's admissibility. Distinguish choosing a presentation, adding an operation, forgetting information, and recognizing an existing semantics. Where a combination is not proved, label it as a possible extension, not a feature of the current calculus.

## 6. Use examples to illuminate the architecture and excite the audience

Examples have at least three jobs: make a general concept graspable, establish that a claimed construction has nontrivial instances, or expose the necessity of a condition.

Distinguish illustration from evidence of applicability. An analogy may clarify a concept without formally instantiating it; label it accordingly. When an example is offered as evidence that the developed machinery applies, exhibit the interpretation from the concrete model to the abstract objects, maps and operations, verify the hypotheses actually used, and show how the advertised result follows through that interpretation. Merely using the framework's vocabulary, or proving a similar-looking claim by an independent calculation, does not establish applicability.

Ask separately what the machinery contributes to the example. Compare it against a credible simpler treatment at the same interface, with the same assumptions and observation requirements. The gain might be a new capability, a reusable proof, a coherent assembly or comparison, or a structural explanation. If the simpler treatment already delivers the claimed payoff and the framework adds none of these, retain the example as pedagogy if useful, but do not promote it into principal evidence of utility. An advantage need not mean that every other method is impossible.

They should not make the framework look as though it was built to solve a contrived fixture.

Prefer an ordinary, persistent running situation that can be revisited as the available structures become richer. The example must have an understandable purpose before its arithmetic or categorical details arrive. An edge case should enter when it tests a previously explained rule. A negative witness should identify the violated obligation and the narrower positive alternative, not merely provide spectacle.

No example should be made to stand for more than it proves. Equality of expected values is weaker than equality of joint laws; a law-level coincidence is weaker than equality of native maps; independent choices are not shared choices; a finite regression does not certify an unbounded theorem. These distinctions belong where the example is interpreted.

## 7. Teach concepts in layers

Consider a **three-layer explanation** for every load-bearing construction.

First give the plain-language role: what the construction is for and what information it retains. Then give the mathematical interface: input data, produced objects and maps, compatibility hypotheses, and direction of comparisons. Finally give the theorem and proof, with its exact quantifiers and boundary cases.

Introduce specialist terminology only when it pays for itself. Define *pure interface*, *context*, *content*, *occurrence*, *native map*, *interaction law*, and *feedback* before relying on them.

A plain-language analogy is useful only if the transferred structure is specified and its limits are clear. Do not replace technical precision with an analogy, but do not make notation the admission ticket to the first page.

Maintain one visual grammar across manuscripts. Reuse distinct shapes or conventions for requirements, produced content, effects, shared state, and observations. Show a diagram of the conceptual architecture early, then let later diagrams refine it. Figures should communicate an invariant or a relationship, not decorate the page.

## 8. Give experts an immediate technical route

Within the abstract or first two pages, an expert should find a compact statement of the known mathematical starting point; the independently supplied inputs; the constructed operation or comparison; what is preserved on noninvertible maps and changing interfaces; the exact hypothesis class; and the nearest related literature.

Distinguish the construction of a mixed law from standard composition *given* a law. Distinguish a native comparison from a quotient of outcomes. Distinguish genuine feedback from sequential state threading, and shared interaction from independent products.

Do not claim historical novelty for a familiar mechanism with new notation. When an imported theorem almost supplies the result, identify the residual mathematical obligation instead of using vague language about unification.

The expert route should be available without making the nonexpert read a taxonomy of pseudomonads, double categories, or alternative completions. A concise contribution map or clearly signposted technical paragraph is sufficient.

## 9. Let manuscript boundaries follow an intellectual argument instead of a proof cluster

A paper should have one coherent central contribution that can be described without internal source names. **The publication architecture should follow the conceptual story. Do not use the repository's very specialized research questions as the starting point for audience motivation**.

Test the organizing premise, not only the clarity of its presentation. Would the intended reader recognize the intellectual opportunity or stakes without knowing the project? Does the premise naturally connect the main results, or are reasons invented to make disconnected findings fit? Do those results actually support the promised story? Compare at least two plausible, materially different framings of the same mathematics: what each makes central, what becomes supporting material, which audience it reaches, and which extra claims it would require. An organizing *claim* or idea is as legitimate as a question; do not manufacture a narrow unsolved problem to justify a general framework. If another framing gives the mathematics more explanatory reach without overstating it, reconsider the paper's structure before editing its sentences.

The archive's file structure, contract stages, and theorem clusters are not publication units by default. A substantial proof can belong in an appendix or technical companion if its role is to establish an ingredient in a larger argument. Conversely, a model-specific construction may deserve its own paper when it has a distinct conceptual advance, reusable theorem, and audience.

Concurrency and feedback are central areas of the programme, not decorative applications of the sequential theory. They also do not yet constitute one automatically unified doctrine.

Manuscript architecture must preserve both facts: explain their relationship to the common framework and state exactly which connecting comparisons have been proved. Do not merge parallel results under an invented umbrella theorem or fragment them into narrowly titled papers merely because the results are technically independent.

For a practitioner-facing treatment, explain what a reader can model, inspect, and check; identify required inputs and assumptions, and clearly separate an executable model from a compiler or real-world system.

For a category-theory treatment, establish the abstraction and its relation to existing mathematics quickly.

For a programme-wide synthesis, prioritize the conceptual structure and supported relationships rather than reproducing every proof.

## 10. Language, pace, and claim discipline

Prefer active, concrete descriptions of mechanisms: which map is constructed, what a condition guarantees, what an observer can distinguish, and how an operation transforms the input.

Avoid unsupported adjectives such as *universal*, *general*, *automatic*, *canonical*, or *conservative*. Each is a theorem claim unless clearly defined and scoped.

Use short paragraphs at the beginning, with only one unfamiliar idea introduced at a time. Later technical sections can be denser, provided the interfaces have already been explained.

Define notation near its use; do not require several pages of symbol definitions before explaining the research. Make titles and section headings answer recognizable questions or describe substantive moves, rather than merely repeat internal theorem names.

Caveats should be placed beside the claim they delimit. They need not dominate the abstract or be repeated defensively after every paragraph.

A precise positive claim, followed by one informative scope boundary, is more credible than either breathless generality or an inventory of everything not proved.

### Make the prose carry the argument

Put each qualification where it changes the meaning of a claim. A **stovepipe pin** names a condition, distinction, or dependency in its own compartment while leaving the reader to work out what it governs. For example, “Shared draw. Scope: fixed law. Composition: conditional.” lists facts without explaining their use. Instead: “For a shared draw with a fixed distribution, compose the stages using their specified joint law conditional on that draw, then average over its distribution. If the stages are conditionally independent given the draw, the conditional joint law is the product of their conditional laws.” This says what is shared, what must be supplied, and what the independence assumption permits. Keep the scope; integrate it into the claim. A table of hypotheses can still help with lookup, provided the argument shows which hypothesis does the work.

Look for drafting notes masquerading as exposition, headings followed by interchangeable mini-essays, and contrasts that correct an inference no reader was likely to make. When flagging a passage, quote the span and name the referent, inference, or consequence it leaves the reader to supply. If a contrast rules out a plausible interpretation, retain it and explain what changes mathematically. No phrase or punctuation mark passes or fails this test by itself.

## 11. Two-pass draft scrub: structure before style

**Scrub the draft in two passes. Fix what it spends time on before fixing how it sounds.**

Read the outline as a reader. Look at the title, opening, section lengths and conclusion. What would someone who never saw the prompt think the paper is about? If a topic appears to be central, name the result, example or decision that earns it that position. A suggestion to include optics is a reason to consider optics. It doesn’t give optics a claim on the subtitle, a tutorial and the conclusion. Keep the material where it answers a question the paper has actually raised.

Then read the prose aloud. Underline the sentence that says something the reader came to learn. Cut the throat-clearing before it and the paraphrase after it. Scrutinize “X, but not Y,” headings that correct an imagined opponent, and repeated assurances about what the reader needn’t know. For example, when the first substantive sentence is “Each construction chooses what counts as a computation…”, start there. The author may have needed the two reminders before that sentence; the reader doesn’t.

Some qualifications do belong on the page. If a theorem assumes independent draws, say so where the theorem is used. If an existing method fails for shared draws, name the failure and show what changes. A real mathematical boundary can survive being stated plainly. Keep drafting reminders in the notes where they can still guide the writer.

Review a run of paragraphs, not just a list of flagged phrases. A page can still sound canned after every “not merely” has been replaced. Listen for the same setup, pivot and recap repeating; repair the whole passage by putting the claims and reasons in the order the reader needs them. Ask what a reader would lose if a sentence were deleted or two adjacent paragraphs swapped. If no dependency changes, cut the redundant sentence or rebuild the sequence around the actual argument. Give the revised passage to someone who hasn’t seen the prompt. Ask where they had to stop, reread, or wait for the point. Use those places to check the edit.

## 12. Editorial review gate

Every manuscript should pass the following tests before polishing typesetting or debating venues:

1. **Ten-second test:** Can an informed newcomer identify the subject, why it matters, and the central idea after the opening passage, without technical vocabulary? In a separate read, stop at the first technical prerequisite in the abstract and again in the introduction. By each stopping point, can the intended reader say what the work is about and what it contributes, without already understanding the machinery?
2. **Two-minute test:** Can that reader explain why the framework is useful and identify one kind of reuse or insight it supports?
3. **Expert connection test:** Can a specialist identify the nearest familiar constructions and the actual mathematical increment quickly?
4. **Unmanufactured motivation test:** Does the motivation survive removal of the showcase example and of internal proof-obligation terminology?
5. **Composition test:** Is the assembly mechanism identified? Are independently successful ingredients being combined by a proved rule, rather than by juxtaposition?
6. **Precision test:** Are domains, codomains, assumptions, map directions, strength of comparisons, and exceptional cases clear at the load-bearing claims?
7. **Breadth test:** Do several materially different instances support the claimed generality, and are any necessary compatibility constraints visible?
8. **Boundary test:** Is there a concrete obstruction or countermodel showing where a tempting stronger interpretation fails, without turning it into artificial motivation?
9. **Evidence test:** Are written, formally checked, executable, empirical, and conjectural statements labeled at their actual strength? Trace each main claim to its exact supporting statement, proof, or check. Match hypotheses and conclusion, not just topic. Give earlier work visible credit for what it supplies; a working link or unchanged citation count is insufficient.
10. **Memory test:** After a day, can a reader recall one coherent central idea rather than only an unusual example, theorem number, or slogan?
11. **Prose and re-entry test:** In a dense passage, can a reader explain why each paragraph follows the last? Enter separately at a theorem, example, or appendix intended to be read on its own. Can the reader recover what it uses and why it is there without reconstructing the development history? Supply a short reminder or an exact route to its premises, rather than repeating the whole setup.
12. **Organizing-premise test:** Is the central idea significant and recognizable to the intended audience independently of the internal research agenda? Does it account for the paper's principal results at their proved scope? Compare alternative organizing ideas before accepting the current one.
13. **Application-validity test:** For each example offered as evidence of applicability, where are the concrete interpretations and hypothesis checks establishing that the claimed construction really applies? Do not count an analogy, naming similarity, or unrelated calculation as an instance.
14. **Incremental-value test:** What does the developed machinery add to the example or the main result relative to a credible simpler method at the same scope? Identify the gain and its added assumptions or costs, without demanding an artificial impossibility proof for the baseline.

### Independent blind review, then informed audit

Before submission, submit the complete rendered manuscript to an LLM in a fresh, isolated session that has no prior exposure to the project. Provide only the manuscript and a neutral instruction such as: “Review this manuscript as a candidate for publication. Choose whatever evaluation criteria seem appropriate to its content and likely audience; support the assessment with passages from the manuscript. Use only the manuscript.” Do not provide repository files, browsing access, author summaries, the prospectus, these guidelines, prior reviews, intended conclusions, or a tailored checklist. The LLM must choose its own initial assessment criteria. Save its first unedited report, the exact manuscript revision, model and prompt before any discussion or follow-up; do not reprompt until a favorable verdict appears. A second independent blind model can help reveal review variance but does not turn agreement into proof.

After freezing the blind report, give an independent reader the rendered draft before showing the author's summary or expected answers. Record their account of the subject, contribution, uses, and limits, including which passages supported that account and where they stopped or reread. Compare this reception with the intended argument and the numbered tests. Then conduct a separate **informed technical audit**, which may inspect the repository, supporting proofs, interpretation bridges, baseline methods, and primary literature. Reconcile conflicting findings at the level of the specific claim or reader experience. Repeat blind review after material changes to the argument or framing, using a new unprimed session.

A blind LLM report tests how a manuscript is received without privileged project context; it is neither a proof certificate nor an authoritative novelty verdict. Automated checks can flag broken links, missing citation markers, and suspicious phrasing. They do not establish that the argument reads well, the cited theorem matches a claim, or the attribution and historical comparison are complete. Those require reading the mathematics and relevant primary work.

Repair at the scale of the failure. Cut an incidental drafting note locally, rebuild a section whose parts do not make an argument, and narrow a claim when its evidence is weaker than the headline. A polished abstract cannot repair a paper whose results have no coherent argument.

##

TODO:

- Conceptual map before theorem map?
- Do not over-emphasize computation, since many of the applications are not really about computation at all, and computers have nice properties that simplify engineering. The work does not really shine with computational examples. Ordinary programming benefits from assumptions that are often unavailable elsewhere: inputs can be copied, computations can be repeated, intermediate results can be stored, and failed calculations can frequently be abandoned without changing the world. Physical processes do not generally permit these conveniences. Measurements disturb systems, experiments consume specimens, actions alter future possibilities, resources cannot necessarily be duplicated, and independent processes interact through an environment that neither controls.
