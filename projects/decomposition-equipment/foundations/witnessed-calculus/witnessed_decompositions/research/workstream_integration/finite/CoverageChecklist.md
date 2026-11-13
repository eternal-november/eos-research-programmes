# Author DOMAIN-to-enumerator preflight response

DOMAIN is unchanged: `d01495686d5f3f01cc635061d7789f64ab0cf5a370571d144971cb819dba52fa`.
This responds line by line to the independent checklist at
`../review/finite_independent_20261025/CoverageChecklist.md`. It is an author
coverage audit, not final C acceptance. Full replay is PAUSED pending parent
release after the reviewer confirms this repaired source freeze.

## Exact code mapping and coverage

| DOMAIN | Source/enumerator | Literal coverage and status |
|---|---|---|
| §1 interfaces | model.Arrow/compose/strings; check.named_controls | Full C/C2 tables, 12 C2 arrows, 120 composable triples; actual grade strings retained. |
| §1 monoids | model.MONOIDS; check.named_controls | Exact Z3/E2/One tables; all elements, pairs and triples; no group-only assumption. |
| §1 graphs/partitions | model.graphs/partitions | All four Graphs(2); every assignment to k ordered slots; empty slots and k=0 case literal. |
| §1/2 constructors | model.L/U/D/C and Flat.valid | Whole graph and grade retained; U only empty identity; empty external L remains a slot. |
| §2 evaluator independence | model.evaluation/address_evaluation/flat_compose | Recursive local substitution, separate root-address traversal, and term-free flat operation; redundant author implementations, not claimed independent authorship. |
| §2 normalization | model.root_steps/steps/measure/normalize/canonical | Seven addressed rules; measure checked; canonical full witness; no semantic equality declared as rewrite. |
| §2 arrow/hom data | model.arrow_key/catalog/tuple_encoder/hom_decode | Original-slot tuple of complete Flat entries; catalog targets generated independently; nonexistent homs also checked. |
| §2 paths/inverses | model.Raw/Eq/path_normalize/semantic_path; check.check_paths | Actual rule/address equations, explicit inverses, raw forest lineage, independent tuple composition; finite verification only. |
| §3 T | check.run_T/check_term/explicit_join | All 18 rows; all graph/partition/C2/value choices; 112785 exact formula cases; all one-step reducts and prescribed O words. Full final replay pending. |
| §4 X bases/contexts | check.x_realizations/contexts/run_X | Exact two graph options, grade patterns, parameter values and 5+|M| surrounding contexts, without semantic deduplication. |
| §4 forest menu | check.forest_menu | Identity, single D_v, every subset/intermediate object/grade binary corolla, eligible labelled nullary, simultaneous D_v. |
| §4 MOut | check.check_mout/residual/run_X | Every contextual base redex and every menu forest, exact same addressed residual, forward and inverse squares. |
| §4 MIn bare arising labels | check.abstract_redex/run_X | Extract EVERY redex of EVERY X base; abstract exact variable positions, retain all cut/graph/grade/value labels; verify grafting back recovers both sides and the full variable profile. Union with the original bare recipe and deduplicate by complete (rule,bare term), not semantics. |
| §4 MIn hosts/instantiation | check.check_bare_case/check_min_pair | Run all host contexts and full forest menu on the complete union. Base, extracted, extra and union counters are separate; no seven-prototype substitution for the arising labels. |
| §4 ordinary disjoint/variable | check.check_bare_case | SAME complete bare-label union; exact addressed two-path checks. Independent expected counts are Odisjoint316 and Ovariable568. |
| §4 overlap joins | check.JOIN_WORDS/explicit_join/eq_trace | All 18 complete author P joining words actually applied; each branch also checked against deterministic normalization. |
| §4 raw two-stage paths | check.run_X | Named six-vertex and two-empty-leaf hosts; all first-menu forests and all prescribed second-stage choices; exact raw forest composition and normalization paths. |
| §5 H | check.run_H; model.tuple_encoder/hom_decode | Every source and target in frozen H, including absent arrows. Formula source count2802; independent reviewer pair count233562. |
| §5 Hcomp/raw | check.run_H/check_raw_flat_pair | EVERY composable Hcomp pair reifies source and entries, performs actual raw forest grafting sequentially and composed, compares each final raw entry against the flat tuple composition, endpoint and hom membership. Named six-vertex pairs use the same check. |
| §6 F | check.run_F/factor_structures/forced_factor/check_factor | All 27270 proper-interval cases; brute candidate intermediate graphs/partitions versus forced-union decoder; complete pair sets, not only fibre counts. |
| §6 named boundary intervals | check.run_F | Six-vertex proper cases30; full, four unary and five empty intervals for every scalar triple; inserted empty slot remains different before nullary substitution. |
| §6 unary/nullary | check.run_F | Every interface and value; all42 source/local unary-to-nullary pairs; labelled nullary values retained. |
| §6 transport | check.check_transport/map_term/map_flat/homs |20 C2 endofunctors, all400 composites per base; all monoid homomorphisms/composable triples; all base equation and raw-menu edges. Per-entry transported profiles are checked explicitly. No assertion that every composite relation word is independently transported in C. |
| §6 normalization under maps | check.check_transport | Mapped normal forms compared AFTER normalization; killing values may remove root D. |
| §6 interface rename | check.check_transport | Both inverse composites for rho:0,1,2↔4,7,9; separate from graph coordinates. |
| §6 graph coordinates | check.graph_coordinates | Identity/phi/psi/composite/inverses at sizes0,1,2,3,4,6; explicit edge/block composites, both inverse directions, and literal nested restriction (G|B)|rank_B(V)=G|V. |
| §6 bound inclusion | check.named_controls | Literal graph data at each of the four T graph types, 2≤6; no vertex permutation. |
| §7 six structure and labels | check.named_six | Both middle splits checked for EVERY source scalar and EVERY four-entry local-value vector:276 assignments, two positional outputs each. Unary tuple cases separately exhaust276 assignments. |
| §7 repeated occurrences | check.named_six | Equal nonempty graph/id components at positions1 and2 remain independently indexed. Both zero-valued and all-labelled raw/flat split comparisons. |
| §7 d0 towers | check.named_six | Four original occurrences plus empty loop, each monoid, heights0..8:135 actual cases. Raw-added count is finite illustration of separate P necessity. |
| §7 nonthin/empty/nullary/grade/partition/whole | check.named_controls/named_six; H/F | Actual nonthin segmentation and scalar tuples; empty L retained; hom across unequal whole grades empty; same leaves/different partition and cross-edge whole separation. |
| §7 localization/movement controls | check.ordinary_localization_control/named_controls | Explicit nonfreely-canceling five-edge pentagon loop without O, scalar-forgetting control, missing-DL distinct normal forms and reverse-rotation cycle. No novel significance implied. |
| §8 actual mutations | run_mutations.MUTANTS/main | Actual source copies and edits; requires exit1 with EXACT intended AssertionError and detecting function; syntax/import/type errors do not count. |
| §8 typed wrong residual | run_mutations.WRONG_TYPED_RESIDUAL | Swap different forest entries ONLY at equal full component types; named six-vertex detection is residual-target inequality, not typing rejection. |
| §8 omitted-MIn targeted probes | mutation_probes.main(omit_MIn) | Each monoid: separate bare and contextual validator rejection, plus all135 finite raw-added-count/semantic-identity instances in mutated copy. An early full-entrypoint failure is not claimed to execute these later checks. |
| §8 labelled-nullary MIn probes | mutation_probes.main(erase_nullary_value) | For each nonidentity value (three cases), first checks a typed MIn-DL unit path using independent address semantics, then detects the recursive-entry value mismatch. |
| §9 counts/cache/logs | check.record/main; verify_certificate | Actual assertion counts; independent formula verification; caches only identical pure values. Partial runs preserved, no domain shrink. |
| §9 fresh replay | pending parent/reviewer release | Final author full run, actual full-source mutants, independent clean replay remain pending; no final PASS inferred from smoke. |

## Preflight evidence only

`SmokeCertificate.json` records a successful NARROW_STAGE_PREFLIGHT_NOT_FULL_DOMAIN:
named controls; first/last X representatives for all T rows and monoids;
complete bare-label catalog extraction (union counts Z3=147,E2=102,One=67),
selected forest instances; every O disjoint/variable instance on that catalog
(316/568); a selected H raw-composition subdomain (8104 pairs); and30 selected
F comparisons. This is not a full T/X/H/F certificate.

`SmokeMutationCertificate.json` records all five intended source-mutant
assertions, plus the explicit targeted probes in their mutated copies. It is
SMOKE_MUTATION_PREFLIGHT_NOT_FULL_DOMAIN, not final mutation acceptance before
a full unmutated pass. The exact actual-source mutation replay and targeted
probes will run again after the final full unmutated certificate.

All historical partial source/log bytes are preserved under history/. The
source02 replay was stopped with terminal exit130 before any later edit, and
has no full-success certificate. Review comments exposed coverage omissions;
they did not motivate a domain reduction or theorem weakening.
