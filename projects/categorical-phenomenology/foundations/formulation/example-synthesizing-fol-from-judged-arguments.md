---
status: >
  Draft worked construction of a candidate first-order realization. Corpus fit, underdetermination witnesses, and a conditional contextual quotient are derived and first-pass checked. Identification of the logical doctrine from judgments remains open; independent verification is pending.
---

# Worked example: constructing a first-order realization of judged arguments

Judged arguments constrain a logical system without uniquely determining it. This example constructs a candidate in an explicitly chosen first-order doctrine, verifies its fit to positive and negative judgments, and derives further consequences. It also exhibits alternative interpretations that fit the same corpus and shows which additional judgments would separate them.

The construction instantiates [two-sided context-sensitive realization](towards-two-sided-context-sensitive-factorization-based-realization.md): arguments are preparations, contexts are tests, and judgments are responses. A candidate supplies a compositional realization of those responses. A response-profile factorization becomes available once complete behavior is specified. Inferring that behavior, discovering a parsing vocabulary, and selecting a logical doctrine from finite evidence remain distinct problems.

## 0. The supplied judgments

| Judgment | Argument-token |
|---:|---|
| ✓ | All humans are mortal. Socrates is human. Therefore Socrates is mortal. |
| ✓ | Socrates is human. Therefore something is human. |
| ✓ | All humans are mammals. All mammals are animals. Therefore all humans are animals. |
| ✓ | Socrates is human. Socrates is Greek. Therefore Socrates is human and Greek. |
| ✓ | Socrates is human. Therefore Socrates is human or Socrates is divine. |
| ✗ | All humans are mortal. Socrates is mortal. Therefore Socrates is human. |
| ✗ | Something is human. Therefore Socrates is human. |
| ✗ | Socrates is human or Socrates is divine. Therefore Socrates is human. |
| ✗ | Every person has some mother. Therefore there is some mother of every person. |
| ✗ | Socrates is human. Therefore everything is human. |

These are supplied labels, not a reported experiment. Read ✓ as an accepted inference and ✗ as a rejected inference, rather than as the truth or falsity of a conclusion. The intended target here is logical consequence under arbitrary interpretations. Biological and historical assumptions are omitted. In the mother argument, take the quantifier domain to consist of persons and interpret the binary relation without further biological axioms. If a judging practice instead relies on background knowledge, pragmatics, or nonuniform judgments, its observation regime must retain those distinctions.

The translations below are proposed readings of the tokens. Supplying them already recognizes names, predicates, connectives, and binding structure; this example does not derive that parsing vocabulary from unstructured language.

## 1. Observations retain judgments after contexts

Let \(A\) be a set of parsed argument situations, and let \(C\) be a monoid of specified transformations \(c:A\to A\), including identity and composition. The monoid presentation applies to total transformations on a fixed interface. Operations changing arity, sorts, or binding interfaces require an indexed family of argument spaces and typed maps instead.

For a fixed judgment function \(J:A\to2\), define

\[
H(a,c)=J(c[a]).
\]

Identity recovers the original label: \(H(a,\mathrm{id})=J(a)\). The corpus provides only a partial table

\[
H_D:O_D\to2,\qquad O_D\subseteq A\times C,
\]

initially containing the ten identity observations. A proposed probe is not an observed result; an unqueried entry is unknown, not false.

Stability can be extracted from this table by comparing \(H(a,c)\) with \(H(a,\mathrm{id})\). It should not replace the table: the stability-only response \([J(c[a])=J(a)]\) is unchanged when all labels are complemented. It therefore loses the distinction between acceptance and rejection.

| Context or probe | Law or distinction to investigate |
|---|---|
| Bijectively rename individuals or predicates, preserving arity and avoiding capture | Invariance in both directions is a candidate law of structural consequence. |
| Permute premises | Exchange is a candidate law; the ten tokens do not themselves test it. |
| Add premises | Weakening preserves acceptance in one direction; rejection may change. |
| Duplicate or remove a repeated assumption | Contraction is a separate candidate law, not a consequence of weakening alone. |
| Substitute terms or formulas without capture | Valid inferences may remain valid; invalidity need not be preserved. Identifying \(P\) and \(Q\) turns \(P(a)\not\vdash Q(a)\) into reflexivity. |
| Replace a unary predicate by a binary relation | Specify the additional argument and its binding before comparing judgments. |
| Swap quantifier order or replace existential information by a named witness | Test whether a distinction matters; do not assume an invariance. |

The laws in this table are hypotheses or methodological choices until supported by additional judgments. Context compatibility will require coherent action on responses, not invariance of every judgment under every transformation.

## 2. Candidate structure and discriminating observations

The accepted instances suggest instantiation, existential introduction, composition of predicate implications, conjunction introduction, and disjunction introduction. The rejected instances require the candidate to preserve distinctions between an implication and its converse, existence and a designated witness, a disjunction and either disjunct, quantifier orders, and a named instance and a universal claim.

These constraints do not yet force the standard connective rules. Two explicit alternatives demonstrate the gap. Keep ordinary nonempty first-order structures and the ordinary clauses for the other symbols, but modify one connective:

\[
\llbracket B\wedge' D\rrbracket=\llbracket B\rrbracket\lor\llbracket D\rrbracket,
\qquad\text{or, in a different candidate,}\qquad
\llbracket B\vee' D\rrbracket=1.
\]

Consequence in either candidate is truth preservation over all such structures. Both candidates are compositional and support identity, weakening, contraction, exchange, cut, capture-avoiding substitution, and the usual quantifier freshness discipline. Both fit all ten labels. The first accepts the sole conjunction-introduction instance but fails projection when \(P(a)\) is false and \(Q(a)\) true. The second accepts disjunction introduction and rejects disjunction projection, but fails \(P(a)\vee'P(a)\vdash P(a)\), which ordinary case elimination derives from two identity proofs.

These are counterexamples to determination by the displayed constraints, not claims about English meanings. They motivate concrete further judgments:

| Additional test | Effect on the displayed alternatives |
|---|---|
| \(P(a)\wedge Q(a)\vdash P(a)\), and the other projection | Acceptance excludes the altered-conjunction candidate. Rejection requires revising the usual conjunction interpretation or the parsing. |
| \(P(a)\vee P(a)\vdash P(a)\) | Acceptance excludes the constantly true disjunction. It does not by itself establish the entire case rule. |
| Case reasoning: from derivations of \(D\) under \(B\) and under \(C\), infer \(D\) under \(B\vee C\) | A schematic acceptance condition supports the full elimination rule; finitely many accepted cases still require a generalization assumption. |

Negative observations exclude overstrong candidates. Positives alone permit an indiscriminate logic, but do not force selecting it. An observed conjunction introduction likewise does not establish a product universal property, and Boolean judgments do not determine identities between proofs.

## 3. Constructing a candidate calculus

For a worked realization, choose the positive intuitionistic first-order doctrine \(K\). This choice supports the corpus while leaving negation and falsity outside the present language. It is a candidate construction, not a conclusion that the corpus selected intuitionistic logic.

Use a relational signature with individual constants, including \(s\) for Socrates, and predicates of specified arities, including unary and binary predicates. There are no positive-arity function symbols and no equality symbol. Terms are variables or individual constants; formulas are generated by

\[
t ::= x\mid a,\qquad
\phi ::= P(t_1,\ldots,t_n)\mid\phi\wedge\phi\mid\phi\vee\phi\mid\phi\to\phi\mid\forall x\phi\mid\exists x\phi.
\]

Bound-variable renaming is identified; substitution avoids capture. Assumption contexts \(\Gamma\) are finite lists, with exchange, weakening, and contraction explicitly admitted. The following constructors generate finite derivation trees \(\mathsf{Der}_K(\Gamma,\phi)\):

| Constructor | Premises and conclusion |
|---|---|
| Assumption | \(\Gamma,\phi\vdash\phi\). |
| Structural rules | Reorder assumptions, add assumptions, or contract repeated assumptions. |
| Conjunction | From \(\Gamma\vdash\phi\) and \(\Gamma\vdash\psi\), infer \(\Gamma\vdash\phi\wedge\psi\); from the conjunction infer either component. |
| Disjunction introduction | From either component infer its disjunction with any formula, under the same assumptions. |
| Disjunction elimination | From \(\Gamma\vdash\phi\vee\psi\), \(\Gamma,\phi\vdash\chi\), and \(\Gamma,\psi\vdash\chi\), infer \(\Gamma\vdash\chi\). |
| Implication | From \(\Gamma,\phi\vdash\psi\), infer \(\Gamma\vdash\phi\to\psi\); from \(\Gamma\vdash\phi\to\psi\) and \(\Gamma\vdash\phi\), infer \(\Gamma\vdash\psi\). |
| Universal elimination | From \(\Gamma\vdash\forall x\phi\), infer \(\Gamma\vdash\phi[t/x]\). |
| Existential introduction | From \(\Gamma\vdash\phi[t/x]\), infer \(\Gamma\vdash\exists x\phi\). |
| Universal introduction | From \(\Gamma\vdash\phi[y/x]\), infer \(\Gamma\vdash\forall x\phi\), with \(y\) fresh for \(\Gamma\) and \(\forall x\phi\). |
| Existential elimination | From \(\Gamma\vdash\exists x\phi\) and \(\Gamma,\phi[y/x]\vdash\psi\), infer \(\Gamma\vdash\psi\), with \(y\) fresh for \(\Gamma,\psi,\exists x\phi\). Discharge the displayed witness assumption. |

The quantifier rules require well-formed, capture-avoiding instances. Universal introduction depends on independence from undischarged assumptions. Existential elimination similarly requires that neither the remaining assumptions nor the conclusion depend on the temporary witness. These are standard natural-deduction restrictions. [✓] Avigad, Hua, Lewis, and van Doorn, [Logic and Proof, §§7.2–7.3](https://leanprover-community.github.io/logic_and_proof/first_order_logic.html), supporting rule passages checked 2026-11-02.

Define \(\Gamma\vdash_K\phi\) by existence of such a finite tree. This is a construction of the least relation closed under the specified constructors: induction on a tree shows that every relation satisfying the same rules contains its conclusion. Derivations compose by replacing open assumption leaves with derivations of those assumptions; rename eigenvariables first to avoid capture. The induced consequence relation forgets distinctions between different derivation trees, while \(\mathsf{Der}_K\) retains them. No proof-equivalence or normalization theorem is asserted here.

This leastness is relative to \(K\). For a different fixed syntax and collection of positive closure rules \(E\), the analogous object is \(R_0=\operatorname{Cl}_E(D^+)\), where \(D^+\) is a set of accepted sequents. It satisfies rejected sequents \(D^-\) exactly when \(R_0\cap D^-=\varnothing\). If the intersection is nonempty, every \(E\)-closed extension violates a negative constraint. None of this defines a minimum across different syntaxes, logical doctrines, or presentation costs.

## 4. Verifying the realization against the corpus

Translate the first-order patterns using unary predicates \(P,Q,U\), the constant \(s\), and a binary relation \(R(x,y)\) meaning that \(y\) is a mother of \(x\). Each row below is a schema standing for the corresponding token; schematic generality belongs to the candidate, while the observations remain the particular supplied labels.

| Accepted pattern | Derivation in \(K\) |
|---|---|
| \(\forall x(P(x)\to Q(x)),P(s)\vdash Q(s)\) | Instantiate the universal at \(s\), then eliminate implication. |
| \(P(s)\vdash\exists xP(x)\) | Introduce the existential with witness \(s\). |
| \(\forall x(P(x)\to Q(x)),\forall x(Q(x)\to U(x))\vdash\forall x(P(x)\to U(x))\) | For fresh \(z\), assume \(P(z)\), instantiate both premises and derive \(U(z)\); discharge \(P(z)\), then generalize \(z\). |
| \(P(s),Q(s)\vdash P(s)\wedge Q(s)\) | Conjunction introduction from the two assumptions. |
| \(P(s)\vdash P(s)\vee Q(s)\) | Disjunction introduction. |

Thus the positives need no extra nonlogical axioms. In particular, the construction does not assert that all humans are mortal without premises: it derives the labeled inference that uses that statement as an assumption.

For negative checks, use ordinary nonempty structures with total interpretations of constants. Atomic formulas receive their usual relational interpretations; \(\wedge,\vee,\to\) use Boolean truth clauses; quantifiers range over the domain. Every constructor of \(K\) preserves truth under these interpretations. This follows by induction on derivations: the propositional and structural steps preserve truth directly; universal introduction varies a fresh variable without changing the assumptions; existential elimination uses a witness whose value cannot affect the remaining assumptions or conclusion. Hence

\[
\Gamma\vdash_K\phi\quad\Longrightarrow\quad\Gamma\models_{\mathrm{classical}}\phi.
\]

Only soundness is used. Classical semantic consequence is not identified with the positive intuitionistic derivability relation.

| Rejected pattern | Countermodel on \(\{0,1\}\), with \(s=0\) |
|---|---|
| \(\forall x(P(x)\to Q(x)),Q(s)\vdash P(s)\) | \(P=\varnothing,\ Q=\{0\}\). |
| \(\exists xP(x)\vdash P(s)\) | \(P=\{1\}\). |
| \(P(s)\vee Q(s)\vdash P(s)\) | \(P=\varnothing,\ Q=\{0\}\). |
| \(\forall x\exists yR(x,y)\vdash\exists y\forall xR(x,y)\) | \(R=\{(0,0),(1,1)\}\): each person has a witness, but no common witness. |
| \(P(s)\vdash\forall xP(x)\) | \(P=\{0\}\). |

Each model makes every premise true and the conclusion false, so soundness rules out a \(K\)-derivation. These witnesses establish compatibility of the combined calculus with the negative data. Checking rules separately would not suffice: a rule \(P\vdash Q\) and another \(Q\vdash U\) can jointly derive a rejected \(P\vdash U\), even when each rule set separately avoids it.

The quantifier-order witness also separates choice from a common witness. The function \(f(x)=x\) explicitly chooses a suitable \(y\) for each \(x\), yet no constant \(y\) works for both elements. An accepted quantifier swap could reflect restrictions on the relation or domain, or an erroneous judgment; it does not by itself establish a different meaning of FOL quantification.

## 5. A further prediction and its derivation

The candidate predicts an inference absent from the corpus:

\[
\forall x(P(x)\to Q(x)),\exists xP(x)\vdash_K\exists xQ(x).
\]

Eliminate the existential using a fresh \(z\) and temporary assumption \(P(z)\). Universal elimination gives \(P(z)\to Q(z)\), so implication elimination gives \(Q(z)\). Existential introduction gives \(\exists xQ(x)\); discharge \(P(z)\) by existential elimination. The conclusion and permanent assumptions contain no free \(z\). This derivation uses no classical principle.

This is a prediction of the chosen candidate, not an additional observed judgment. Rejection would require checking the parsing, background assumptions, reliability of the judgment, and the chosen rules. The quantifier-order invalidity in §4 is already in the corpus and therefore supplies no new out-of-sample test. The connective probes in §2 specifically distinguish the displayed alternative realizations; none of these tests alone identifies a unique logic.

## 6. The contextual factorization

Let \(S_K\) be the set of formal argument situations \((\Gamma,\phi)\) in the chosen language, and let \(r_K:A\to S_K\) be their specified interpretation. On already formal arguments \(r_K\) is identity. For each admitted source context \(c\), supply its action \(\bar c\) on \(S_K\) with

\[
r_K(c[a])=\bar c(r_K(a)).
\]

This requirement makes context translation part of the realization. For the transformations defined through the parsed syntax it holds by construction; a new natural-language transformation requires its own correspondence. Define

\[
J_K(\Gamma,\phi)=[\Gamma\vdash_K\phi],\qquad
q_c^K(\sigma)=J_K(\bar c(\sigma)),\qquad
H_K(a,c)=q_c^K(r_K(a)).
\]

The proofs and countermodels establish \(H_K|_{O_D}=H_D\). The brackets denote a mathematical yes/no relation, not an assumed decision procedure for arbitrary first-order provability. \(H_K\) completes the observed table according to the candidate; its unobserved entries have not thereby become empirical facts.

For any complete behavior \(H(a,c)=J(c[a])\) with the monoid action of §1, form

\[
a\sim_H b\iff\forall d\in C,\ H(a,d)=H(b,d),\qquad
S_H=A/{\sim_H}.
\]

The response-profile map factors as a surjection followed by an injection:

\[
A\twoheadrightarrow S_H\hookrightarrow2^C,\qquad
[a]\longmapsto(d\mapsto H(a,d)).
\]

This quotient supports the context action because

\[
H(c[a],d)=J(d[c[a]])=H(a,d\circ c).
\]

If \(a\sim_H b\), composition closure gives equal responses on the right for every \(d\); hence \(c[a]\sim_H c[b]\). Therefore \([a]\mapsto[c[a]]\) is well-defined. This is the framework's context-compatibility law with \(c^*(d)=d\circ c\).

The kernel identifies exactly arguments having the same complete contextual judgment profile. It forgets lexical and derivational differences only insofar as these tests cannot distinguish them. Applying it to \(H_K\) constructs the observational states of the candidate's behavior. Agreement on the finite observed entries alone does not justify that quotient: future contexts can split an apparent equivalence class.

The logical-rule closure in §3, this response-profile image, and an FCA closure of probe attributes are different constructions. An observational quotient does not independently supply a syntax or a logical doctrine. A stronger Kan-extension or cylinder-factorization account would additionally require observable and internal categories, realization morphisms, designated factorization classes, and the relevant existence and preservation results.

## 7. A categorical interpretation of the chosen logical structure

Let \(\mathcal C\) have variable contexts as objects and well-typed term substitutions as arrows. These variable contexts are distinct from the assumption lists \(\Gamma\) in derivations. Formulas whose free variables lie in \(\Theta\), ordered by \(\phi\leq_\Theta\psi\) when \(\phi\vdash_K\psi\) and identified under mutual derivability, give fibers of a contravariant doctrine \(\mathcal P:\mathcal C^{op}\to\mathsf{Pos}\). Reindexing is substitution. For a context projection \(\pi:\Theta\times X\to\Theta\), the quantifier rules express

\[
\exists_\pi\dashv\pi^*\dashv\forall_\pi.
\]

Explicitly, for \(\phi\) in context \(\Theta,x:X\) and \(\psi\) in \(\Theta\), the adjunctions are

\[
\exists x\phi\leq_\Theta\psi\iff\phi\leq_{\Theta,x}\pi^*\psi,
\qquad
\pi^*\psi\leq_{\Theta,x}\phi\iff\psi\leq_\Theta\forall x\phi.
\]

Existential introduction and elimination prove the two directions of the first equivalence; universal introduction and elimination prove the second. The condition that \(x\) is absent from \(\psi\) is enforced by its context. Here \(X\) is the single individual sort of the chosen language.

The corresponding substitution laws are Beck–Chevalley conditions: substituting for the other variables commutes with quantification after capture-avoiding renaming. Conjunction, disjunction, and implication supply their chosen fiberwise operations. Full Heyting hyperdoctrines are a standard setting for the extension including falsity; the positive fragment used here does not add falsity or equality merely by invoking that setting. [✓] Awodey and Bauer, [Introduction to Categorical Logic, Chapter 3](https://awodey.github.io/catlog/notes/catlog3.pdf), especially §§3.1.4 and 3.4, supporting passages checked 2026-11-02.

This explains how the chosen rules support a structured realization. It does not show that the ten labels force that structure or establish a universal property for a category of realizations of the partial evidence. Comparisons between candidates must specify which operations they preserve; preserving provability alone need not preserve rejection, which requires reflection on the relevant sequents.

## 8. Preserved distinctions and remaining choices

The construction deliberately uses schematic predicates and names, arbitrary nonempty domains with total constants, and structural assumptions reusable and discardable without cost. These are declared choices. The corpus fits them, but does not independently establish the associated general invariances. The negative checks retain implication direction, the difference between named and arbitrary individuals, existential information versus a designated witness, disjunctive information versus an individual disjunct, and quantifier scope. The temporary witness discipline preserves dependencies on assumptions.

Before choosing \(K\), the data also leave equality, positive-arity functions, denotation conventions, and resource-sensitive alternatives open. Nonemptiness is fixed for this candidate by its ordinary semantics and total constants; a free-logic candidate would need its own denotation rules. A regime rejecting weakening or contraction cannot satisfy the present structural doctrine unchanged. Negation and falsity would have to be added before testing excluded middle or explosion. Quantification over predicates would further require a choice between full and restricted semantics. An unexplained appeal to intensional predicate identity does not determine a modal or type-theoretic extension.

Boolean judgments retain admissibility, not proof identity, normalization, or computational content. Those outputs need extra requirements or evidence. Likewise, discovery of syntax, selection among logical doctrines, and noisy or contested judging remain outside this exact construction. The supported result is a constructed candidate with all ten labels verified, explicit alternatives showing nonidentification, a further derivable prediction, and a context-compatible quotient relative to complete behavior.
