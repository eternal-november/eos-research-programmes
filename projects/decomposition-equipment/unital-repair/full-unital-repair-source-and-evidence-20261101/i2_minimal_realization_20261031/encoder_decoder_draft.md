# I2 candidate: effective codecs and independent semantic checks

**31 October 2026. Implementation candidate, conditional on the selected-fragment gate.** This addresses the effective-realization/independent-decoder tests of original I2 (contract lines 638–653). It is not acceptance of unrestricted I2, a new proof of I5 discreteness, or an implementation of the old graph calculus.

## 1. Precise input/output contract

Input is an exact old operation record `s`, its full ordered profile/frame/actual witness data, and a tuple of concrete labels indexed by its nonempty input **occurrences**. Empty positions are retained in `s`; two equal labels at different occurrences remain two tuple entries. Each admitted old graft/cut/transport supplies its actual old output record and occurrence maps. The old algorithm must verify that skeleton's admissibility. Neither the code nor the theorem infers old admissibility from a label grouping.

The output is `(s, code_1,...,code_r)`. No profile or old-record identification occurs. Finite coefficient tables are shared implementations across sorts, not a finite global state carrier. Unbounded empty arity and unary depth are allowed. If a concrete old record's validation is not effective, the coefficient kernel does not remedy that defect; effective realization is relative to the old effective-record implementation. Its runtime includes reading that unbounded record.

The fixed probes are the original first-channel readout, declared channel-swap transport, actual one-hole grafts, and set-valued **whole ordered joint factor-class tuples** of each permitted old cut. Generated tests are finite compositions/Boolean combinations and laminar cut trees. No crossing/shared-variable-across-subtrees extension or counts are asserted.

## 2. M_k encoder, decoder, and finite algebra interpreter

Let `t=k-1`, `k>=4`. Codes are `A_i,B_i (0<=i<=t)` and `D_i (0<=i<=t-2)`. The encoder accepts an actual vector `(f(0),...,f(k-1))`; it does not assume a generator word or identify a function by enumerating the normal-form decoder.

1. Recognize the identity directly as `A_0`.
2. If `f(1)=2`, recognize constant 2 as `B_t`; otherwise check that `f(0)=1`, every value is 1 or 2, and the positions with value 2 on `{1,...,t}` form an initial interval of length `i+1`. Return `B_i`.
3. If `f(1)=1`, set `i=k-f(0)` and check `1<=i<=t` and `f(x)=max(1,x-i)` for all positive x. Return `A_i`.
4. Otherwise recognize `D_i` by `f(0)=2` and a positive-input initial interval of 1s of length `i+1`, followed by 2s, with `0<=i<=t-2`.
5. Reject all other vectors.

This is O(k) input comparisons. The independent function decoder uses the closed coordinate formulas of I5 `monoid_repair_theorem.md` §1. It reconstructs the actual transformation (this is legitimate precisely because the endpoint on M_k is discrete). The operation interpreter implements the normal-form multiplication table, without calling concrete composition or re-encoding a decoded function. Original local observation is `i==0` (membership in `{A_0,B_0,D_0}`); for two channels use only the first code's index, exactly as originally specified. Swap exchanges the two channel codes.

The verifier constructs the reference M_k by breadth-first closure of actual function composition under the concrete a,b generators. It then checks every concrete function's round trip and every product against the separately written table. Thus neither agreement nor carrier size is certified by merely generating and recognizing the same normal forms. The all-k proof is the explicit normal-form distinctness/coverage argument in I5; finite checks are regression evidence, not that proof.

For `M_k×M_k`, apply the encoder/decoder/table componentwise. A rank-r fibre requires `(3k-2)^(2r)` states. This state count and its necessity are **imported I5 results** (`profile_schemata_theorem.md` §4); the I2 contribution here is the executable semantic interface and its commuting diagrams, not a rediscovery of discreteness.

## 3. Compressed group control: decoder is not recovery of hidden state

Let `G=C4×C4`, written as pairs modulo 4, with code group `Q=C2×C2`. Encode `(u,v)` as `(u mod 2,v mod 2)`. Original observation decoder is the **first** code coordinate. Quotient multiplication is pairwise addition modulo 2; transport swaps coordinates. The initial readout sees only first parity; the allowed transport exposes second parity. Hence the code has four states per active occurrence and is the minimal simultaneous observable quotient in the declared control family. Rank r has `4^r` quotient states but `16^r` concrete label assignments.

The optional representative section maps a bit pair to the same integer pair in `{0,1}²`. It obeys `encode(section(q))=q`, but it is neither an inverse encoder nor generally a group homomorphism: a representative of `1+1 mod2` is 0, while representative addition modulo4 gives 2. The executable verifier explicitly exhibits `section(encode((3,2))) != (3,2)`. The realization's decoder means observation readout and semantic interpretation, not fictional recovery of the original hidden group element.

## 4. Joint-cut interpreter and proof for every generated test

For a supplied actual old cut with active grouping sizes `(r_1,...,r_m)`, the decoder enumerates outer codes `a_1,...,a_m` and inner code tuples `b_ij`, retaining exactly those satisfying `x_ij=a_i b_ij` in the quotient. The same chosen `a_i` is reused for all j. Outputs are `(outer tuple, tuple of inner tuples)` with positions retained; the API never returns independent marginals. Its finite brute-force bound is `p^(m+r)<=p^(2N)` candidate assignments on the coefficient carrier p, for one fixed old cut; it makes no finite enumeration claim about all old skeletons.

For discrete M_k labels, pointwise decoder bijectivity and the multiplication commuting square imply exact agreement of these joint relation tuples with concrete cuts. For group compression, soundness follows from the quotient homomorphism. For completeness **at a fixed concrete source**, take a quotient cut and choose one lift `a_i` of each outer quotient label. Set `b_ij=a_i^{-1}x_ij` using that same parent for all children. Quotient equations force each resulting child's prescribed code. All labels decorate the supplied skeleton by the independent-extension hypothesis. Thus every quotient joint tuple is realized at every representative source, not just at some representative or separately per child.

These elementary identities imply every generated contextual observation by structural induction: constants and initial observations decode correctly; graft nodes commute by the multiplication square; transport nodes commute by swap; cut nodes use the complete paired source-fixed lifting above, and induction interprets child tests while keeping the parent-selected factor witnesses. This proves finite laminar cut-tree semantics at arbitrary depth. Boolean operations preserve equality. If the probe syntax permits equality of hidden labels or crossing constraints between separate subtrees, that is a different probe family requiring a fresh proof.

Composition of full typed operations uses the caller's actual old graft and the branch formula `a_i b_ij`. Therefore this is a typed compositional operation quotient equipped with an existential joint-cut relation, conditional on the old interface. It is not descent of actual witness multiplicities, unique lifts, CULF, or an objective decomposition span. The code tests the coefficient kernel; full graph-engine execution is not represented as tested.

## 5. Independent checks and exact extent

Run `python verify_encoder_decoder.py`; standard library only. `encoder_decoder_results.json` records the result.

* k=4 through 12: closure-generated concrete carrier, size `3k-2`, every encode/decode round trip, and every multiplication pair against the independently written normal-form table.
* For each k: the index Q is verified cut-stable, but `e ~Q b` while `a e` and `a b` have different indices. Initial H observation agrees on e,b and on their left-a graft outputs; a subsequent Q cut signature separates the latter. The analytic index-cut hierarchy supplies the fact that Q itself is definable by finite generated pure-cut tests, hence this is a genuine cut-after-graft separator, not a newly authorized index sensor.
* k=4, every ordered two-source tuple: direct concrete shared-parent cuts versus coded shared-parent cuts. All tuples—not separate marginals—are compared.
* All C4² concrete binary products and swaps: parity commutation; original observation decoder checked on all 16 hidden values.
* Every source and grouping template at ranks 1–2, plus every grouping at ranks 3–4 with two chosen source tuples including repeated occurrences: quotient cut enumeration compared with independent concrete modular subtraction for each shared parent. This is 552 template/source checks; it is **not** an exhaustive check of all rank-three/four sources. The structural source-fixed lifting proof covers all ranks/sources. Rank-zero cut output is checked as the singleton `{((),())}`, not the empty set.
* A group graft with repeated children is performed and then cut in the compressed interpreter; its originating joint tuple is retained. Different old profile tags stay distinct, and repeated equal labels keep two occurrence entries.

The k,N family proof, exact M_k class lower bound, group compression, and uniform `R(k)+4` round upper bound (all-label multiplier palette) are imported with their original hypotheses from I5. No fixed finite experiment proves unbounded coverage by itself. The minimality/uniqueness theorem and finite-index criterion belong in the accompanying I2 theory artifact; this implementation supplies its explicit realizations.


## 6. Generic finite CLOSED typed constructor and certificate evaluator

`finite_typed_realization.py` accepts explicitly finite carriers by sort, initial observation values, total typed deterministic context maps, and named joint-cut relations whose outputs are complete tuples of typed nodes. It rejects dangling targets and missing source rows. It refines by old class, operation-target class, and full sets of output-class tuples until stable, then emits the typed codebook, observation decoder, induced operation tables and quotient joint-cut tables. Every row is checked against **all** representatives; source-fixed back-condition equality is checked explicitly. A finite input is required to be closed under the declared operations/cuts; this is not a truncation theorem for arbitrary graph profiles.

The constructor also retains a DAG of characteristic class predicates. Seed nodes are original observation predicates. A stage node conjoins its prior class predicate, deterministic successor predicates, and exact cut-signature predicates. Exact signature equality is the finite conjunction of existential tuple predicates for present tuples and their negations for absent tuples over the finite output-class/shape universe. The evaluator recursively checks this certificate against the original concrete relations, without consulting the final code assigned to the queried node. Memoization avoids re-expansion of the DAG. Checking every final class predicate at every concrete node independently verifies the codebook's classification.

An additional explicit formula AST evaluator supports original-observation equality, negation, conjunction, deterministic precomposition, and existential **one-record** joint cuts with a list of positional child formulas. It operates on either the concrete model or the generated quotient; the latter is the executable observational decoder. Repeated positions in a tuple are not deduplicated; a nullary joint tuple satisfies the zero-child conjunction, while an empty relation does not.

Current executable generic test: the finite CLOSED unary M4 model with left/right a,b and complete binary factorizations gives ten classes; 100 final class/node certificate evaluations and 200 concrete-versus-quotient formula evaluations pass. A separate two-sort nullary control verifies exact sort tags and the distinction between `{()}` and no cut. This test does **not** claim the finite unary model is the full multicategory. The all-profile realization uses the analytic coefficient codec above plus the old guard/operation implementation and structural induction. Group compression tests are in the separate codec checker; no claim is made that the generic constructor was run on all group rank sorts.


The finite constructor additionally provides `all_slot_contexts`: given an explicit total finite multioperation table, it expands **every** slot and every assignment to its other slots into a deterministic one-hole map. For claiming a finite multioperation quotient the caller must use that complete expansion (or prove its supplied generating contexts suffice); a convenient subset is not silently sufficient. The check also runs refinement on all left/right multipliers of M4, independently of the a,b-generated context test. Exported certificate definitions and seed-observation literals permit another implementation to evaluate the DAG without the constructor callback or final codebook. Class labels in a definition are references to previous-stage formulas, not authorized observation atoms.
