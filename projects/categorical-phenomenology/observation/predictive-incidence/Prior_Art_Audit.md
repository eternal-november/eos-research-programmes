# Primary-source audit: predictive reconstruction, incidence completion, and experiment choice

Audit date: 3 November 2026. Read against the baseline in `phenomenology_emergence_20261103/report.tex`. This is a source-level comparison, not a claim that a literature search establishes novelty or absence.

## 1. Conclusions that should affect the report

1. **The basic bridge is established.** Myhill–Nerode row identification and the Galois/factorization completion of the same prefix–suffix incidence are explicitly compared in the universal-automaton literature. The previous report's embedding of residuals into their intersection closure is a useful baseline, not a research advance.
2. **Actively learning the completion is established.** Björklund, Fernau and Kasprzik give observation-table learning of the canonical universal automaton with membership and equivalence queries. NL* already makes row inclusion and union decomposition determine hypothesis construction and new suffix tests. Barlocco, Kupke and Rot provide a coalgebra–logic duality framework for active learning.
3. **Column reduction has two genuinely different objectives, but both are classical.** Preserving the equal-row partition is a distinguishing-test/indiscernibility problem. Preserving the labeled extent closure is FCA attribute reduction. Their difference can support a clear theorem or counterexample; merely recognizing that difference is not strong evidence of novelty.
4. **The proposed balanced permutation family has an unusually close precursor.** Hospodár–Mlynárčik's binary permutation-DFA reversal witness has exactly the binomial-size orbit of balanced test extents. Universal automata already have tight exponential size relative to minimal DFAs. A comparison of the two reduction objectives should be stated as a corollary or independently proved synthesis unless a further result survives the audit.
5. **The partial-column feasibility test is elementary closure theory.** Existence of a closed extension between positive and negative observations is equivalent to the least closure avoiding the negatives. This is directly adjacent to partial-context realization and conjunction learning. A membership-probe policy differs from an implication oracle, but that does not make the closure lemma new.
6. **The threshold monotonicity candidate also has exact-oracle precedent.** Damaschke (1995) reconstructs a promised-monotone discrete function in linear many threshold queries. The proposed no-promise decision procedure is a simple scan-and-abort extension. Its separation is from identification of arbitrary maps, not identification restricted to monotone maps.

## 2. Keep the mathematical objects typed

For a language L, define the one-sided incidence u I v iff uv belongs to L. Equal rows give residual predictive states. Formal concepts are maximal pairs (P,Q) with PQ contained in L; right factors Q are intersections of residuals. Standard FCA ordering by P-inclusion reverses Q-inclusion.

This is different from the two-sided incidence (l,r) J u iff lur belongs to L. Equal columns there give syntactic congruence, while its Galois completion is the **syntactic concept lattice**. An assertion about one incidence does not automatically apply to the other.

Also distinguish the nondeterministic canonical **universal automaton** built from all maximal factorizations from an automaton whose acceptance condition requires all runs to accept. Both are called universal automata in different literatures. The Björklund–Fernau–Kasprzik source below concerns the former.

Finally, a lattice with exponentially many elements, an irredundant set of exponentially many raw test columns, an exponentially expensive explicit output, and an exponential oracle-query lower bound are four different claims. None follows from another without additional arguments and a specified representation model.

## 3. Audited primary sources

### A. Clark: explicit DFA/Galois comparison and the different two-sided lattice

Alexander Clark, *The Syntactic Concept Lattice: Another algebraic theory of the context-free languages?*, Journal of Logic and Computation 25(5), 1203–1229, 2015; online 2013. [Author PDF](https://alexc17.github.io/static/pdfs/JLC2013.pdf), [DOI](https://doi.org/10.1093/logcom/ext037).

The introduction and Table 1 explicitly juxtapose prefix–suffix row equality (minimal DFA) with prefix–suffix Galois structure (UA), then distinguish these from context–substring syntactic congruence and the SCL. Section 7.1, Definition 7.6, describes UA states as maximal factorizations. Section 3 develops the SCL through closure/Galois constructions; Proposition 3.22 states finiteness iff regularity.

**Comparison:** This directly anticipates extracting a predictive partition and a richer hierarchy from the same observations at the full-language level. It does not identify the one-sided UA lattice with the two-sided SCL. Its mathematical input is a language; it does not, by itself, provide a finite membership-only identification certificate.

**Confidence:** High: full author PDF inspected. Use the introduction for the precise two-column comparison, not a vague attribution that all concept lattices are predictive state spaces.

### B. Lombardy and Sakarovitch: exact intersection construction and size blow-up

Sylvain Lombardy and Jacques Sakarovitch, *The Universal Automaton*, in *Logic and Automata: History and Perspectives*. [Author PDF](https://perso.telecom-paristech.fr/jsaka/PUB/Files/TUA.pdf), [published open chapter](https://www.jstor.org/stable/j.ctt46mv83.17).

Proposition 2.1 gives right factors exactly as arbitrary intersections of left quotients, and the dual statement. Definition 2.4 gives transitions by XaY' contained in L. Section 4 constructs the UA from a DFA through co-determinization and intersection closure. Section 5 states the tight 2^n bound relative to an n-state minimal DFA; a unary nonzero-length-modulo-n language attains it. Thus completion can be much larger even without multiple input generators.

**Comparison:** This is a direct precedent for deriving the complete incidence structure once a transition-certified predictive model is known. It also blocks treating the mere exponential completion blow-up as new. Its UA transition relation is nondeterministic; do not silently identify it with the deterministic inverse-image action on the entire intersection closure used in the earlier report.

**Confidence:** High for the inspected statements. The author PDF labels a 2007 version with different page numbers from the published 2008 listing; cite section/proposition numbers and the published bibliographic record consistently. It is an author-written synthesis with proofs, not the earliest source of every theorem.

### C. Lombardy: original size theorem

Sylvain Lombardy, *On the Size of the Universal Automaton of a Regular Language*, STACS 2007, LNCS 4393, 85–96. [Publisher primary page](https://link.springer.com/chapter/10.1007/978-3-540-70918-3_8).

The primary abstract states a tight Dedekind-number bound in terms of smallest equivalent NFA size and an exponential-of-Landau-function bound in the unary case.

**Comparison:** Prior work studies the succinctness gap between finite recognizers and canonical factorization completion quantitatively. This is not the same parameter as the number of selected distinguishing columns or number of empirical queries. For the exact 2^n DFA statement, the previous source supplies the inspected proof context.

**Confidence:** High for abstract claims; subscription full paper not inspected. No stronger theorem details are attributed here.

### D. Wurm: a genuine cross-construction isomorphism with hypotheses

Christian Wurm, *Automatic Concepts and Automata-Theoretic Semantics for the Full Lambek Calculus*, LACL 2016, LNCS 10054, 308–323. [Open publisher full text](https://link.springer.com/chapter/10.1007/978-3-662-53826-5_19).

Theorem 16 proves ACL(U(L)) is isomorphic to SCL(L): the automatic concept lattice built using the universal automaton matches the two-sided syntactic concept lattice. Section 4.4 explicitly warns that no such simple structural relationship holds for arbitrary accepting automata. Soundness of its semantics requires the stated nuclear-automaton condition.

**Comparison:** This is stronger than merely observing that automata and concepts share an incidence matrix. But it concerns the automatic transition-relation construction on U(L), not an unconditional identification of the minimal DFA with a concept lattice. It is not a theorem about selecting unknown empirical tests.

**Confidence:** High: full text and theorem inspected.

### E. Björklund–Fernau–Kasprzik: active learning of canonical universal automata

Johanna Björklund, Henning Fernau, Anna Kasprzik, *MAT Learning of Universal Automata*, LATA 2013, LNCS 7810, 141–152. [Publisher](https://link.springer.com/chapter/10.1007/978-3-642-37064-9_14). Journal version: *Polynomial inference of universal automata from membership and equivalence queries*, Information and Computation 246 (2016), 3–19. [DOI](https://doi.org/10.1016/j.ic.2015.11.005). [2012 author preprint](https://www.uni-trier.de/fileadmin/fb4/INF/TechReports/ratom2longelsevier.pdf).

Published abstracts state observation-table learning of the canonical UA with polynomial query count measured in UA size. The preprint uses known alphabet, exact membership queries and global equivalence queries returning counterexample words; it extends prefixes/suffixes and enforces stability and saturation. It explicitly compares its construction with L*.

**Comparison:** Active acquisition of a Galois/factorization completion is already an explicit research subject. Polynomial in UA size can be exponential in DFA size. Equivalence queries are substantially stronger than a finite batch of reset-word experiments.

**Source caution:** The inspected preprint is older than the publication and contains a suspect ancillary assertion in Remarks 6–7 that all factors are row or column factors, false for general relations. Do not rely on those remarks or transplant its fine-grained bounds without checking the version of record. The published abstract independently verifies the core prior-art claim.

### F. NL*: inclusion and algebraic row structure drive new tests

Benedikt Bollig, Peter Habermehl, Carsten Kern, Martin Leucker, *Angluin-Style Learning of NFA*, IJCAI 2009, 1004–1009. [Proceedings PDF](https://www.ijcai.org/Proceedings/09/Papers/170.pdf), [institutional preprint record](https://www.isp.uni-luebeck.de/research/publications/angluin-style-learning-%C2%A0nfa).

NL* learns the canonical residual finite-state automaton with membership and equivalence queries. States correspond to prime residuals, which are not unions of other residuals. Observation rows are compared by inclusion; closedness and consistency concern that structure. A witnessed failure of consistency supplies a letter-prefixed suffix to add to the test set. Final correctness is canonical RFSA identification, not merely a table fit.

**Comparison:** A generic proposal to use order/closure failures in the shared observations to request further experiments is already close to NL*. Its algebra is union/prime-residual structure, not arbitrary intersection completion. The exponentially smaller RFSA is not generally the smallest NFA. Distinguish target guarantees from interim hypotheses.

**Confidence:** High for these statements; publisher search indexing supplied paper text, while direct PDF fetch through the web tool failed. No claim about a new query bound is needed here.

### G. Coalgebra learning via duality

Simone Barlocco, Clemens Kupke, Jurriaan Rot, *Coalgebra Learning via Duality*, FoSSaCS 2019, LNCS 11425, 62–79. [Full author text](https://arxiv.org/html/1902.05762), [DOI](https://doi.org/10.1007/978-3-030-17127-8_4).

Logical formulas serve as tests through a dual adjunction between states and logical theories. A table contains selected states and a subformula-closed test collection; counterexample formulas expand the tests. Theorem 6.4 gives reachable, logically minimal, correct output upon termination. Theorem 6.6 requires the logical quotient to have finitely many quotients and subobjects for termination. The generic setting treats systems beyond DFA, including bisimulation learning for labeled transition systems.

**Comparison:** A categorical state/test comparison that guides learning is established. Important access difference: the generic learner can locally explore successors of selected states and read the underlying transition structure. The paper explicitly distinguishes this from accessing states only by appending letters to histories. Its hypotheses cannot be transferred to an arbitrary black-box experimental apparatus without specifying how those operations are implemented.

**Confidence:** High: full text, access discussion, and theorem statements inspected.

### H. FCA attribute reduction

Bernhard Ganter and Rudolf Wille, *Formal Concept Analysis: Mathematical Foundations*, Springer, 1999, §1.2, especially pp.24–27, Definition 24 and Proposition 12. [Institution-hosted full book](https://math.ubbcluj.ro/~csacarea/wordpress/wp-content/uploads/Prof.-Dr.-Bernhard-Ganter-Prof.-Dr.-Rudolf-Wille-auth.-Formal-Concept-Analysis_-Mathematical-Foundations-1999-Springer-Verlag-Berlin-Heidelberg.pdf).

An attribute is removable when its extent is an intersection of other attribute extents. Removing it preserves the concept lattice. Clarification removes duplicate rows/columns; finite reduced contexts are unique up to isomorphism and use irreducible object and attribute concepts.

**Comparison:** The test-column conjunction-redundancy criterion is the standard FCA reduction criterion. It is stronger than retaining only equality distinctions among the existing rows. The preservation here has a canonical labeled-extent interpretation; an arbitrary abstract lattice isomorphism should not be conflated with preservation of the observational meaning of objects.

**Confidence:** High: book downloaded and relevant text inspected. The web renderer rejected the large file size, but direct public download succeeded.

### I. Modern reduction audit explicitly points back to basic FCA

Jan Konečný, *On attribute reduction in concept lattices: Methods based on discernibility matrix are outperformed by basic clarification and reduction*, Information Sciences 415–416 (2017), 199–212. [DOI](https://doi.org/10.1016/j.ins.2017.06.013).

Jan Konečný and Petr Krajča, *On attribute reduction in concept lattices: The polynomial time discernibility matrix-based method becomes the CR-method*, Information Sciences 491 (2019), 48–62. [Publisher](https://www.sciencedirect.com/science/article/pii/S0020025519302415), [DOI](https://doi.org/10.1016/j.ins.2019.03.038).

The latter abstract says that eliminating unnecessary discernibility-set computations reduces the method essentially to standard clarification and reduction. This is a warning against relabeling standard column elimination as a new discovery.

**Confidence:** Abstract/bibliography level; publisher full pages return 403. Prefer the inspected Ganter–Wille construction for the mathematical claim, rather than deriving theorem-level details from these abstracts.

### J. Partial contexts and implication-guided completion

Franz Baader, Bernhard Ganter, Ulrike Sattler, Barış Sertkaya, *Completing Description Logic Knowledge Bases Using Formal Concept Analysis*, IJCAI 2007, 230–235. [Primary full text](https://ijcai.org/proceedings/2007/35).

Definitions 2.1–2.4 treat positive/negative partial descriptions, realizers, implication refutation and implicational closure. The procedure propagates accepted implications and asks an expert to decide undecided implications or supply partial counterexamples. Theorem 2.11 gives its completion guarantee under the expert assumptions. Unknown entries are not interpreted as false.

**Comparison:** The transpose of a partially known new attribute is a partial object description. A proposed closure-based query rule fits this existing consistency/realization setting. But the source's oracle decides implications against a full intended domain; it is not a promise that finitely many individual incidence probes can certify a universal implication over an open object domain.

**Confidence:** High: definitions and algorithm inspected. Publisher metadata says pages 230–234 whereas conventional citation often says 230–235; use the primary record's page range if exact pagination matters.

### K. Generalized attribute exploration

Daniel Borchmann, *A General Form of Attribute Exploration* (2012). [Full author text](https://arxiv.org/html/1202.4824), [stable record](https://arxiv.org/abs/1202.4824).

The framework generalizes exploration using closure operators and partial descriptions. Section 2 states the least implicational closure construction and positive/negative partial-object semantics. Section 3 distinguishes implications already entailed, already refuted, and questions needing an expert.

**Comparison:** Closure propagation and choosing undecided tests are not new in themselves. This remains an implication/expert learning interface unless additional membership-only machinery is proved. The HTML rendering shows an anomalous generated date, but the arXiv submission record is February 2012; use that record for chronology.

**Confidence:** High for inspected definitions and scope, not a claim that this paper states the exact proposed new-column theorem verbatim.

### L. Distinguishing tests in classical conformance testing

Tsun S. Chow, *Testing Software Design Modeled by Finite-State Machines*, IEEE Transactions on Software Engineering SE-4(3), 1978, 178–187. [Primary paper copy](https://archiv.infsec.ethz.ch/intranet_secured/r/1/chow-testingFSMs.pdf), [DOI](https://doi.org/10.1109/TSE.1978.231496).

Definition 7 defines a characterization set as input sequences distinguishing every state pair of the minimal reference automaton. The testing result combines such distinctions with transition coverage and a bound on implementation states.

**Comparison:** A selected column set that preserves predictive state distinctions is a characterization-set objective. A small characterization set does not itself certify the transition graph, reachability, or global equivalence. This source operates with output FSMs, so map its observations carefully to the terminal-Boolean model rather than silently claiming identical costs.

**Confidence:** High for the definition and hypothesis distinction; this audit does not assert an optimal characterization-set theorem.

### M. Exact balanced-orbit precursor

Michal Hospodár and Peter Mlynárčik, *Operations on Permutation Automata*, DLT 2020, LNCS 12086, 122–136. [DOI](https://doi.org/10.1007/978-3-030-48516-0_10), [full proceedings, paper at PDF pp.131–145](https://www.lirmm.fr/~ochem/lietard.pdf).

Lemma 7 uses a cycle and transposition generating the symmetric group and transitivity on fixed-cardinality subsets. Theorem 11(d) gives the tight binomial(n,floor(n/2)) reversal complexity, using a balanced final set and binary permutation transitions.

**Comparison:** For a DFA the reverse subset states are exactly the distinct preimages δ_w^{-1}(F), which are the raw test extents on its states. Therefore the proposed exponential family of balanced extents is already realized by the source's witness. The FCA irreducibility inference and the comparison with a logarithmic separating subfamily are additional simple deductions, not a new orbit construction. Neither the source nor this inference alone proves a learning-query lower bound.

**Confidence:** High: the construction and reversal proof inspected in the full proceedings.

### N. Exact threshold-query predecessor

Peter Damaschke, *Searching for a monotone function by independent threshold queries*, ISAAC 1995, LNCS 1004, 284–290. [Primary publisher abstract](https://link.springer.com/chapter/10.1007/BFb0015433).

The oracle is exactly whether f(x) is at least y. For a promised-monotone discrete f with domain size m and range size n, m≤n, the paper reconstructs f using O(n) threshold queries and arithmetic operations, with O(log n) parallel time and independent simultaneous queries.

**Comparison:** Linear threshold-query reconstruction on monotone functions is established. A no-promise decision procedure requires rejecting nonmonotone inputs, which the abstract does not itself address; a sequential scan-and-abort supplies that extension immediately. The proposed Ω(n log n) lower bound concerns arbitrary maps and does not apply after imposing monotonicity.

**Confidence:** High for the primary abstract's exact oracle/model/result. Full subscription text not inspected. Citation year is 1995 despite the publisher's 2005 electronic-publication date.

### O. Monotone automata and the known-order distinction

Marek Szykuła, *Checking Whether an Automaton Is Monotonic Is NP-complete*, CIAA 2015, LNCS 9223, 279–291. [Author paper](https://arxiv.org/abs/1407.5068), [DOI](https://doi.org/10.1007/978-3-319-22360-5_23).

The paper defines monotonic automata by existence of a linear order preserved by each input letter and notes that letter preservation implies preservation by every word. Deciding existence of some suitable order is NP-complete, even for binary alphabets.

**Comparison:** The candidate supplies the order in advance, so its query procedure is not solving the NP-complete problem. Inverse images preserve all upsets iff a map is order preserving; on a finite chain the principal threshold upsets already test this equivalence. Applying this to derivatives gives the proposed no-new-extent characterization by elementary order theory.

**Confidence:** High for definitions and stated complexity; no transfer of the NP-completeness result to the candidate is suggested.

## 4. Candidate-specific deductions and restrictions

These deductions are independently checked; they should not be represented as verbatim theorems of the sources above.

### Fixed-domain distinction: preserving states versus preserving all concepts

Let H be a fixed object/history set and E a complete family of Boolean test columns. Keeping E0⊆E preserves row equality when every pair separated by E is still separated by E0. Keeping E0 preserves the labeled extent closure when every omitted column extent is an intersection of retained extents. The latter implies the former: each omitted bit is a conjunction of retained bits.

The converse fails already for two rows (1,0),(0,1). Retaining just the first column preserves their distinctness. The full extent closure is {H,{h1},{h2},∅}; the retained one is {H,{h1}}. This is a basic FCA-versus-discernibility contrast, not evidence of a new theorem. It also shows that a new column can enrich concepts without splitting any old row class.

For n=2^k states and all n/2-subsets as test extents, every column is irreducible under intersection of other columns: any distinct same-size column fails to contain it. Yet k selected balanced coordinate subsets distinguish all states. The symmetric-group DFA realizes these extents. Hence an exponential gap between raw FCA attribute retention and predictive distinguishing-column retention follows. It is a **representation/reduction gap on a fixed complete state context**, not by itself a gap between optimal learning algorithms. It does not count experiment word lengths, access sequences, transition checks, or equivalence certificates.

### Partial new column

Let C be the old extent closure on fixed H. Let P,N⊆H be disjoint confirmed positive and negative responses for a pending column. Then

    some C0 in C satisfies P⊆C0⊆H\N  iff  cl_C(P)∩N=∅.

Necessity follows from leastness of closure; sufficiency chooses C0=cl_C(P). If h∈cl_C(P) is probed and returns 0, no old conjunction can represent the new column. If h is already positive, that probe conveys nothing new. A meaningful policy probes unobserved h in cl_C(P)\P and must account for admissibility/cost.

Predictive splitting is forced by the partial data iff an old equal-row class contains both a positive and a negative observation. Otherwise extend the column constantly on each old class. This statement concerns a single new Boolean column, no required transition consistency, and a fixed object domain.

The two feasibility tests can guide different queries, but their existence is not an optimization theorem. To claim an improved active strategy requires an explicit cost model, admissible query set, stopping criterion, comparator and proved advantage. Positive answers at every inspected h do not certify redundancy on an unbounded uninspected domain.

### Threshold-chain candidate

Suppose all n labeled states and their known order are supplied, observations include all threshold predicates, and an individual query returns whether δ(i)≥j. The old closure is the chain of threshold upsets (with endpoints as specified). It is invariant under inverse image by δ iff δ is order preserving; closure under all iterates then follows from closure under one step.

A sequential procedure can maintain the exact preceding value t. First check δ(i)≥t; reject on failure. Otherwise raise t while querying the next threshold until the exact value is known. Across an accepting run t rises at most n−1 times, and each row contributes only a constant number of boundary/validation queries. Thus O(n) queries decide monotonicity, and on accepting runs reconstruct the whole map. The same bound holds before an early rejection.

There are n^n arbitrary maps, so binary-answer exact identification over all maps needs at least n log2 n worst-case answers. But the number of nondecreasing maps is binomial(2n−1,n), with only O(n) bits of entropy. The gap is therefore a property-versus-unrestricted-identification distinction. It does not establish that closure information can be certified cheaply while predictive transitions remain unknowable on the positive instances: this algorithm knows them all there.

## 5. Remaining source-level limits and useful leads

- The published 2016 UA-learning article's full proof should be checked before relying on exact complexity details; the inspected 2012 preprint is not a safe substitute for every theorem.
- *On the connection of hypergraph theory with formal concept analysis and rough set theory*, Information Sciences 330 (2016), 342–357, [DOI](https://doi.org/10.1016/j.ins.2015.09.054), explicitly treats complete k-uniform hypergraphs, reducts and indiscernibility partitions in its primary abstract. This is a particularly relevant further check for the balanced-extent separation. Full text was inaccessible in this pass, so no exact overlap is asserted.
- Damaschke's threshold result assumes monotonicity; no exact citation asserting the no-promise scan-and-abort decision variant was located. That absence is not evidence of novelty: the extension is elementary and the oracle is identical.
- Finite observations, full infinite language structure, supplied known state set, successor access, reset-word access, implication experts, and equivalence oracles must remain separate assumptions throughout the report.
- No source search here establishes that a sharpened theorem or a well-specified algorithmic comparison is new. A credible novelty claim needs a nontrivial statement surviving these mappings, not a more general description of familiar constructions.
