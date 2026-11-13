# Exact resource-observation criterion in Lean

This is a **manual formalization**, not machine-generated proof discovery or literal list-certificate replay. It extends the separately checked sufficiency proof without changing that source. It formalizes the three-way equivalence in the resource-observation analysis's Section 7.

## Exact statement and assumptions

Let M be any type, le a reflexive/transitive relation, and add a binary operation monotone jointly in its two arguments. No finiteness, commutativity, associativity, identity, antisymmetry, or decidability is assumed. In particular, the result applies to every ordered commutative monoid.

For profiles U,V define

    Product(U,V)(b) iff there exist x,y with U(x), V(y), and le(add(x,y),b).

Profiles are upward with respect to le. B is any observation region, including empty B. The checked theorem proves the equivalence of:

1. **Universal agreement preservation:** whenever two pairs of upward profiles agree on B, their products agree on B.
2. **Observed-factor domination:** whenever b belongs to B and add(x,y)≤b, there are a,c in B with x≤a, y≤c, and add(a,c)≤b.
3. **Exact restriction:** at each observed output budget, the product of any upward profiles agrees with the product computed using their B-restricted inputs.

Under transitivity the product itself is upward, proved in the base file. Therefore statement 1 is a congruence on upward profiles. In an ordered monoid this product is the upward closure of the Minkowski sum.

## Why necessity is not circular

For each x, use the principal upward profile {z : x≤z} and its observed upward saturation {z : there is a in B with x≤a≤z}. Reflexivity and transitivity show these profiles are upward and agree on B. Universal product agreement, the antecedent of the necessity implication, then supplies an observed-saturation product witness. Monotonicity moves its larger factors back down to the observed factors, producing exactly condition 2.

The final theorem is a proved biconditional. Neither compositionality nor factor domination is a globally assumed axiom. The separate restriction-exactness equivalence needs only reflexivity and transitivity, not monotonicity of add.

## Verification

- `ResourceObservation.lean` is the unchanged reviewed base source, SHA-256 `2bce2dd651117adf12e29edf967f91422cf0aea422549552063ec4a1e8f1e57a`, with 10 axiom-free theorems including concrete positive and negative controls.
- `ResourceObservationIff.lean` adds 7 axiom-free theorem declarations, including the three equivalences and their supporting lemmas.
- Lean 4.35.0 compiles both. No custom axioms or admissions are used.
- `AuditSignatures.lean` prints the elaborated predicate definitions and complete theorem signatures, including implicit parameters, and repeats the three equivalence axiom audits.
- A deliberately corrupted necessity proof that skips the monotone transport of the factor witnesses is rejected by Lean.
- `independent_review.json` records a separate source/assumption review; `validation.json` records compiler version and source hashes.

This proves exactly the written criterion. It does **not** formalize the nucleus characterization, all quantale/matrix/closure laws, the ordered-group obstruction, bounded-refund repair, controller/selector synthesis, or novelty relative to earlier literature. It does not verify that any empirical evidence genuinely covers all admissible profiles. The formalization uses standard logical and order reasoning; no discovery-efficiency claim follows.

## Reproduce

Use Python 3 and an existing Lean 4.35.0 executable. No mathlib, package manager, or network access is needed.

```sh
LEAN_BIN=/path/to/lean python validate.py
```

If Lean is on PATH, `python validate.py` suffices. The script rebuilds the base module in `.build/` before checking the extension and its negative test. Files in `negative_tests/` intentionally do not compile. No prebuilt Lean module is required or included.
