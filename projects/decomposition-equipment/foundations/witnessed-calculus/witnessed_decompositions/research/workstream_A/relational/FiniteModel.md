# Typed finite second target and oracle domain

Evidence C, author-tested submission for A2; not full A2 acceptance and not C2 completion. The uniform arbitrary-carrier relational-calculus theorem is `RelationalTargetProof.md` (P). The executable is `check_relational_model.py` (Python standard library only). Full report: `FiniteChecks.json`; console record: `finite_oracle.log`.

## Exact signature and carriers

This uses the independent `audit/WorkstreamAReview.lean` schema without editing that file:

- Interfaces a,b,c are distinct.
- Components x:a→b, r:b→b, y:b→c, tail:b→c, whole:a→c are distinct full components.
- Every component carries Bool={0,1}; in particular r is nonempty and value-bearing.
- root : [x,tail] → whole.
- tail : [r,y] → tail.
- fork : [r,r] → r.
- red,blue : [r] → r are distinct parallel primitive witnesses.
- erase : [] at b → r is an explicitly enabled nullary primitive.

All operation records contain the output full component and complete ordered path, including endpoints. The Python constructors check composability and exact output/profile equality. Equal carriers never induce a coercion. The matching Lean schema remains an independent integrated syntax reference, not a claim that these Python records are Lean terms.

The first relational assignment alpha has the following relations (a predicate here specifies the full table, not a terminal Boolean):

- root(x,t;z) iff z=x XOR t, or x=t=1. Thus root(1,1) has BOTH outputs 0,1.
- tail(r,y;t) iff t=r XOR y.
- fork(r0,r1;r) iff r=r0 AND r1.
- red(0)={0}; red(1)={0,1}.
- blue(0)={1}; blue(1)={0,1}.
- erase()={0,1}.

The second legal assignment beta differs ONLY at the primitive red: beta(red)=alpha(blue). In particular, the same declared red witness has two distinct legal images in its exact fibre. Both images are genuinely multivalued at input 1. The assignments to all other primitives, including blue, are identical.

## Witness-retaining syntax target and nontrivial evaluations

The base syntax is

    root(x, tail(fork(r,r),y)).

Its four external leaves are the ordered mixed path x,r,r,y. Graft the red corolla into the first r occurrence and the blue corolla into the second, leaving x and y as identity edges. This gives the nested four-leaf tree

    N = root(x, tail(fork(red(r),blue(r)),y)).

Then:

- At red's corolla input 0, alpha outputs {0}, beta outputs {1}.
- At N input (x,r0,r1,y)=(0,0,0,0), alpha outputs {0}, beta outputs {1}.
- Under alpha at input (0,0,1,0), N outputs {0}, while the tree with red and blue swapped at the two r occurrences outputs {0,1}.

These are two distinct strict extensions once the generic A2 theorem is instantiated with the P-constructed relation target. Distinctness already follows by restricting to the corolla; the nested calculation shows it is not confined to an isolated primitive. The repeated slots both carry values and receive independent substitutions. Swapping them retains a legal typed frontier but changes semantics, so the test detects component-name lookup masquerading as occurrence-indexed substitution.

The independent C syntax comparator retains every generator and child position. Its identity assignment sends every primitive to its own corolla and fixes all nine tested trees literally. A second syntax assignment changes only red's image to blue's corolla; its extension changes both red's corolla and N as trees. For each of the nine trees, the following change-of-assignment square is checked as equality of entire relation tables:

    eval_alpha(syntax_extension_red_to_blue(T)) = eval_beta(T).

The syntax extension is implemented by corolla grafting, not by replacing relation outputs. This is a finite comparison against witness-retaining syntax using the same schema as the integrated syntax target. It does not replace the lead's generic Lean extension/strictness/uniqueness theorem.

Nullary tests include erase's own relation, erasing the first repeated r in the base, and erasing both. Their frontiers are respectively [], [x,r,y], and [x,y]. The nullary witness remains a real vertex and its chosen outputs remain observable in the relation. It is not treated as an identity edge. In particular an identity on r has a singleton input, not an empty input.

## Independent finite oracles

Three genuinely different evaluation routes are recorded:

1. `join_mask` enumerates tuples in the outer relation and compatible rows of each inserted relation, takes their ordered Cartesian product, and projects away the intermediate outputs. It stores the complete resulting relation mask.
2. `truth_mask` enumerates every candidate final input tuple/output and every intermediate Bool tuple, slices inputs by local arities, and checks the membership formula. It does not call `join_mask` or its row decoder.
3. `global_eval` assigns one variable to each syntax edge occurrence, enumerates all values of internal edges globally, and conjoins the local generator-table constraints. It does not call either relational substitution implementation or the recursive tree evaluator.

All 18 tree evaluations (nine trees, two assignments) compare recursive substitution against route 3 on the entire table. The exhaustive substitution table compares routes 1 and 2.

### Exhaustive finite domain, fixed before reading results

Carrier Bool. At every vertex, range over EVERY subset of Bool^arity × Bool, independently at each occurrence. The number of relations of arity 0,1,2 is respectively 4,16,256.

For associativity, outer arity n ranges over 0,1,2; each middle arity m_i ranges over 0,1; each bottom arity l_ij ranges over 0,1. These choices include genuine binary outer relations, arbitrary unary nondeterminism, empty relations, universal relations, and nullaries at all three levels. Flattened arity is at most 2. This is a stated finite arity domain, not a purported exhaustive check of arbitrary trees or all arities.

- Both units for all 276 relations: 552 equalities.
- All compositions of an outer relation of arity at most 2 with independent inner relations of arity at most 1: 4 + 16·20 + 256·20² = 102,724 full-table comparisons between routes 1 and 2.
- All associativity equations in the three-level domain: 4 + 16·(4+16·20) + 256·(4+16·20)² = 26,879,044 full-table equalities.

The mask domain is the value-level relation domain. Because all carriers here are the same two-element set, the same table equations instantiate any LEGAL endpoint-typed tree shape with these arities; it is not claimed that the exhaustive mask loop itself checks all paths. Full boundary validity is checked separately in the mixed-interface example and negative certificates. Arbitrary dependent carrier types and transports are handled by the P proof, not inferred from this common-carrier enumeration.

## Explicit rejection and mutation certificates

Seven expected `ValueError` certificates are required; absence of an exception fails the run:

1. A red image with a different parallel output component, despite the same endpoints/carrier.
2. A root image whose legal path is [x,y] rather than [x,tail], despite identical endpoints and arity.
3. Reversed root inputs [tail,x], which are not a legal composable path.
4. A nullary relation with nonloop output x:a→b.
5. A replacement with output x instead of r at the second repeated occurrence of fork.
6. A binary fork relation assigned to unary red.
7. Reversed syntax children at root.

Three semantic mutations must be detected:

- If repeated equal-color occurrences are forced to use one shared intermediate value, fork[red,blue] at (0,0) wrongly becomes empty rather than {0}.
- If the two legal same-color substitutions are silently swapped, fork[red,blue] at (0,1) becomes {0,1} rather than {0}.
- If the equality identity is replaced by the universal unary relation, red composed with that supposed identity has a different full table (indeed universal), violating the unit law.

These are mutation-sensitive negative controls, not assertions about valid model laws. The executable intentionally implements each mutation separately, then asserts that its result differs from the valid operation. All failed typing messages and distinguishing input/output tables are retained in the JSON report.

## Reproduction and assurance boundary

Run from the project directory:

    python research/workstream_A/relational/check_relational_model.py --output research/workstream_A/relational/FiniteChecks.json

The standard-library-only run prints counts and runtime. The saved JSON includes the executable's SHA256 and Python version. `--skip-exhaustive` is a smoke option and explicitly reports `NOT RUN` for exhaustive checks; `Smoke.json` is not used as the exhaustive certificate. Relation outputs are complete masks/tables, never merely success flags. No outside services, publishing, costs, or local files outside this evidence directory are touched.

The checks establish the claimed finite equations and rejection behavior. They cannot establish the uniform calculus theorem, arbitrary-target freeness, all model-family requirements, semantic completeness of an equational theory, graph-cut nonreconstruction, or C2 classification. Those remain outside this certificate. All results await independent review.
