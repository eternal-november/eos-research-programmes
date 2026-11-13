# Audit of the proposed exact-square and budget-convolution theorem

## Verdict

The general criterion is Guitart exactness, an established characterization of pointwise Beck–Chevalley. The additive-budget matrix result is a concrete elementary specialization with three useful, genuinely different levels. It should be presented as an explicit classification derived from known exactness, not as a new general categorical principle. This audit checks the formulas supplied by the parent, not an unseen finished manuscript.

## Precisely matched prior art

Batanin–Kock–Weber, *Regular patterns, substitudes, Feynman categories and operads*, TAC 33(7) (2018), §2:

- Lemma 2.2 reduces exactness of a small lax square to the corresponding Yoneda Kan-extension test.
- Lemma 2.4 characterizes exactness by connected factorization categories; its convention includes nonemptiness. The authors attribute the criterion to Guitart (1980).
- Theorem 2.11, with its smallness/admissibility and algebraic-cocompleteness hypotheses, relates monoidal exactness, monoidal Kan extension and strong restriction for presheaf Day convolution. For covariant budget functors use the appropriate opposite-category convention; the strict additive square itself has no ambiguity.

Primary theorem text verified at https://webercat.au/rpfc.pdf, PDF pp. 10–15. The original historical citation is René Guitart, *Relations et carrés exacts*, Ann. sc. math. Québec IV(2) (1980), 103–125; this original paper was not independently read in this audit.

Official Mathlib has a directly matching formal API: `TwoSquare.guitartExact_iff_final`, `guitartExact_iff_isConnected_rightwards` and `TwoSquare.instIsIsoFunctorLanBaseChangeOfGuitartExact`. Its square has exactly the orientation T⋙R ⇒ L⋙B. These are source documentation checks, not a claim that the new project proof has been mechanized.

https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/GuitartExact/Basic.html

https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/GuitartExact/KanExtension.html

## 1. Identification of the proposed square

Let A=∏ᵢAᵢ, B=∏ᵢBᵢ, u=∏ᵢuᵢ, W:A→A₀, V:B→B₀ and χ:Vu⇒u₀W. For a∈A₀ define

Fₐ:(W↓a)→(V↓u₀a),

(x,h:Wx→a) ↦ (ux, u₀(h)∘χₓ).

For d=(b,f:Vb→u₀a), an object of d↓Fₐ is exactly a triple (x,h,k), with h:Wx→a, k:b→ux, and u₀(h)χₓV(k)=f. Arrows are arrows between the x's preserving both displayed triangles. This is the proposed lift/factorization category. Nonempty connected lift categories say precisely that Fₐ is final. There is no new notion of cofinality here.

Finality implies that the pointwise comparison

Lan_W(u*X) → u₀*Lan_V(X)

is invertible for every Set-valued X:B→Set. Restricting the assertion to external products X=⊠ᵢXᵢ does not weaken the criterion: products of the covariant representables Bᵢ(bᵢ,−) are the covariant representables B(b,−). For such a test, the target colimit is B₀(Vb,u₀a), while the source colimit is the disjoint union, over f:Vb→u₀a, of π₀(d↓Fₐ). The comparison is the obvious map to f. Bijectivity is exactly one connected component in every lift category.

This argument also states the smallness assumption needed to form these colimits. It does not require every external-product functor to be arbitrary, because representables already detect the condition.

## 2. Witness categories: stronger, but specify what the witnesses are

If the retained witness object is the full indexing/category-of-elements construction, equivalence for every input diagram is stronger than Set-colimit equality. Constant singleton input diagrams expose Fₐ itself, so equivalence of all such witness comparisons requires Fₐ to be an equivalence. Conversely an equivalence transports categories of elements after the corresponding restriction, so it suffices.

This is a classification of formal decomposition/allocation witnesses. It does **not** yet identify them with the project's native execution occurrences, resource ownership, endpoint squares, proof cells or physically executable plans. Such an identification needs a declared interpretation and a proof of its lifting/coherence properties. In particular, a final functor may collapse nontrivial higher homotopy, and even a category equivalence does not recover a narrower source grammar by itself.

## 3. Additive ordered budgets

Use Nᵏ as the poset category with coordinatewise order, tensor + and unit 0. For covariant X,Y:Nᵈ→Set,

(X⋆Y)(a)=colim_{p+q≤a} X(p)×Y(q).

Let C be a d×m matrix of nonnegative integers. At source budget a∈Nᵐ, the allocation functor is

Dₐ:Alloc(a)→Alloc(Ca), (r,s)↦(Cr,Cs),

where Alloc(a)={(r,s):r+s≤a}, ordered componentwise. The lift category over (p,q) is the finite poset

L(a;p,q)={(r,s):r+s≤a, p≤Cr, q≤Cs}.

### Boolean preservation

Boolean Day convolution is existential reachability of a supported pair. Universal comparison equality is equivalent to every L(a;p,q) being nonempty for p+q≤Ca. Principal upper-set tests at p and q detect necessity.

The condition is: **every column of C is either zero or a standard basis vector.**

Necessity: set a=eⱼ. If a column v has total coordinate sum at least two, split v=p+q with p,q both nonzero (if a coordinate is ≥2 split that coordinate; otherwise use two positive coordinates). The only source allocations use the one source unit on the left, right, or neither; none can supply both positive p and q.

Sufficiency: each source unit maps either to nothing or to one unit of one target resource. For each target row allocate enough of its available source units to p and then q; p+q≤Ca guarantees enough units. Leave unused units unallocated. This constructs an actual integer allocation, not just a counting argument.

### Set-colimit preservation

The condition is: **every column is zero or a standard basis vector, and no two nonzero columns have the same target row.**

Necessity beyond the Boolean condition: if two columns j,k equal eᵢ, take a=eⱼ+eₖ and p=q=eᵢ. There are exactly two feasible lifts, allocating j left/k right or k left/j right. They are incomparable and disconnected. Principal representable tests expose two source colimit elements mapping to one target element.

Sufficiency: with at most one nonzero column per target row, every nonempty lift poset has a least element: place pᵢ units into r at the unique source column mapping to i, qᵢ units into s there, and set all zero-column allocations to zero. Every other lift lies above it. Thus it is nonempty and connected (indeed contractible), proving the exact-square condition.

### Full allocation-category equivalence

The condition is: **every column is a standard basis vector and all target rows of columns are distinct.** Zero columns are now forbidden.

If column j is zero, at a=eⱼ the three different allocations (0,0),(eⱼ,0),(0,eⱼ) all map to (0,0). The source is a nontrivial poset; the target is terminal. They are not equivalent categories, although the functor is final and all Set-colimit comparisons can still be exact. With no zero column and distinct row images, Dₐ is a poset isomorphism onto Alloc(Ca): unused target rows are forced to be zero. This proves sufficiency. Equivalence would imply Set exactness, ruling out all remaining bad columns and duplicate rows.

## 4. What this adds to the project and what it does not

- The explicit matrix trichotomy is a useful sharpened example: splitting one source unit breaks Boolean existence; merging two distinguishable source units breaks Set-level uniqueness after connected-component quotient; erasing a source dimension may preserve all Set colimits but breaks the full allocation category.
- It specializes the same distinction already central to O7: observation reflection can be exact while reconstructing original witnesses only laxly or not at all. It does not replace O7's raw-zero/possibility conditions.
- O1 already demands Beck–Chevalley and proves strong parameter-change transport for full relative modules. The new finality criterion belongs to Set colimits and cannot be substituted for O1's invertible native mates without an independent module-level comparison theorem.
- FCA and Dowker outputs have additional map-class and support constraints. Exactness of this Kan square does not by itself imply that a transported test family is Chu-compatible, concept-dense, support-preserving, or topologically equivalent.
- Neither published general exactness nor this classification should be described as an effective algorithm for inventing a new signature. The matrix and the allowed allocation category are supplied.

The proof above is self-contained mathematical analysis of the candidate. A finite exhaustive check is supplied separately as a regression check, not as the proof.
