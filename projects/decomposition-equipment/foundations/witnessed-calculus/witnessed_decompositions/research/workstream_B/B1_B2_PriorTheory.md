# B1/B2 prior-theory and contribution ledger

Checked 24 October 2026. This is a bounded provenance/comparison pass, not an
exhaustive novelty search. No novelty is claimed for B1/B2. These obligations
are shared infrastructure under the unchanged contract, not separate major
integrated-result bundles. Source checks inform attribution; the mathematical
proofs and Lean axioms do not depend on remote pages remaining available.

## Established baselines

1. **Free multicategory and planar-tree infrastructure.** Tom Leinster,
   *Higher Operads, Higher Categories* (2004), Appendices D (free multicategories,
   pp. 389–395) and E (tree representations, pp. 396–398), is the already named
   A1/A2 baseline. Those constructions are not newly invented here.
   [Author's arXiv record](https://arxiv.org/abs/math/0305049),
   [publisher's Appendix D](https://www.cambridge.org/core/books/abs/higher-operads-higher-categories/free-multicategories/6FF0B781CC35A8862B20D7570AA3C5E0).
2. **Linear extensions and adjacent independent swaps.** Colin Defant and Noah
   Kravitz, *Friends and Strangers Walking on Graphs*, arXiv:2009.05040v2,
   Proposition 1.3, p. 3, explicitly gives connectivity of finite-poset linear
   extensions under the adjacent toggle operations. The paper itself treats
   this as known. B1 supplies its own short induction and, separately, proves
   why actual legal typed corolla executions are the linear extensions of the
   forest's ancestry poset. Merely citing connectivity would not establish that
   execution correspondence. [Primary paper](https://arxiv.org/pdf/2009.05040).
3. **Category of elements.** David Spivak, *Category Theory for Scientists*,
   author/course text dated 17 September 2013, Definition 4.6.2.1, p. 194,
   defines the category of elements of a covariant set-valued functor: objects
   pair a base object with an element, and arrows are base arrows taking that
   element to the prescribed target. This is established categorical machinery.
   [Author's MIT course text](https://ocw.mit.edu/courses/18-s996-category-theory-for-scientists-spring-2013/9cf51d1394fc107baa6764d553dd0bb6_MIT18_S996S13_textbook.pdf).

## Exact comparison with the category-of-elements baseline

The following identification is our explicit application of the cited general
construction, not a quotation or claimed new general theorem. Fix outer
interfaces A,B. Form the typed forest category whose objects are paths p:A→B
and whose arrow p→q is an occurrence tuple (b_i), one operation outputting each
edge of p, with concatenated profiles exactly q. Composition substitutes the
next tuple into each b_i; its laws are proved entrywise from `Calc`, with A1's
nested occurrence correspondence. This is `RefinementForest` in the B2 source.

For a fixed whole c:A→B, assign to p the operation fibre M(p;c). A forest b:p→q
acts by a↦a[b]. The identity and associativity laws make this a covariant
set-valued functor. Its category of elements has objects (p,a∈M(p;c)) and
arrows b with a[b]=a'. Passing between total operations and their profile fibres
using accepted A1 identifies it exactly with `Ref(M,c)`. Thus the generic
semantic category is a category-of-elements instance, not a new kind of
category. The library gives explicit tuple formulas and checked type transport
rather than invoking that general construction without proving its inputs.

## Result-level contribution accounting

| Target | Strongest applicable baseline | What this checkpoint actually supplies | Immediate use and failure-sensitive certificate |
|---|---|---|---|
| B1 raw category/poset | Free planar syntax and tree-prefix order | Actual forest arrows; unique recovery, thinness and antisymmetry; component/order-preserving occurrence coherence checked for the accepted representation | B2 raw/free identification; repeated identical components with different substitutions would be corrupted by label-only indexing |
| B1 chronology | Finite-poset linear-extension connectivity | Independent legal execution definition; complete two-way correspondence with tagged forest ancestry; stable addresses versus changing frontier ranks, including arity zero | Explains exactly what B1 arrows forget; dependent-child and nullary-rank negative controls detect the omitted conditions |
| B2 general comparison | Category of elements of a substitution action; functoriality of strict maps | Arbitrary typed tuple category and evaluation functor, operation-injectivity and entrywise-liftability criteria, explicit separation from automatic raw-source faithfulness | Used immediately to interpret the actual A3 associative quotient certificate; a composite-only arrow equality would wrongly collapse its unequal tuples |
| B2 nonthin certificate | Associativity quotient of free binary trees | Actual generated A3 quotient with arbitrary typed associativity family and surviving unary witness statistic; mixed-interface parallel arrows and a fixed-target nonlifting proof | Demonstrates why raw thinness, quotient object identification, and semantic arrow tuples are distinct; motivates but does not solve/activate B3 |

These results can close the stated infrastructure obligations if independent
review accepts their complete evidence. They do not amount to new general
multicategory, trace, or category-of-elements theory. A4 remains local/open;
the A4/B3–B4/C5 integrated scientific floor is unchanged and unsatisfied by this
checkpoint. No contribution count or completion percentage is inferred from
lines of Lean, finite test counts, elapsed time, or the number of lemma names.
