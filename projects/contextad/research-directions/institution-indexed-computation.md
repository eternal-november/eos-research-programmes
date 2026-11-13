# Institution-indexed computation

> Exploratory proposal, not an established globalization theorem. The discussion identifies additional base-change, interaction-preservation and satisfaction obligations; it does not amend the research contract.

Grothendieck institutions and O1 solve different composition problems. The interesting possibility is to combine them: Grothendieck institutions handle changing logical systems, while O1 handles interacting computational effects. Together, they could support computations whose underlying logic, available operations, and interpretation of observations change during execution.

## 1. The connection

A Grothendieck institution starts with a diagram of logical systems, each represented as an institution:

\\[ \mathcal I_i=(\mathrm{Sign}\_i,\mathrm{Sen}\_i,\mathrm{Mod}\_i,\models_i). \\]

The diagram also specifies translations between those systems.

The Grothendieck construction assembles them into one heterogeneous institution:

\\[ \mathcal I^\sharp=\int\_{i\in J}\mathcal I_i. \\]

An object of its signature category is a pair \\((i,\Sigma)\\): a logical system together with a signature belonging to it. Morphisms can incorporate translations between different logical systems.

Crucially, the construction retains the identity of each component logic and respects satisfaction across translations. This is established mathematics, developed particularly by Răzvan Diaconescu and Till Mossakowski.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://imar.ro\&sz=32)

Simion Stoilow Institute of Mathematics+1



Now compare O1.

The inherited computation paper has context structures \\(M\\) and content structures \\(N\\). O1 constructs an interaction

\\[ \tau:N\odot_C M\Longrightarrow M\odot_C N \\]

that makes their combined sequential computations coherent.

The distinction is:

|                         | Grothendieck institutions                    | O1                                                  |
| ----------------------- | -------------------------------------------- | --------------------------------------------------- |
| What is assembled?      | Different logical systems                    | Different computational effects                     |
| What must be respected? | Sentence/model translation and satisfaction  | Composition, dependencies, grades, and native cells |
| What results?           | One heterogeneous institution                | One combined computation structure                  |
| What is not automatic?  | New interactions between logical connectives | Compatibility of independently specified effects    |

These are complementary rather than interchangeable constructions.

## 2. There is already a direct Grothendieck connection in the paper

The inherited paper's Section 8 contains a Grothendieck extension construction:

\\[ (\mathcal P_KY)(A) = \int\_{P\in K_A}Y(e_AP). \\]

It assembles context-indexed categories into a larger presheaf-level construction and recovers the original context computations on representable objects.

So the resemblance is not merely philosophical. Both developments use the mathematics of indexing, fibrations, and Grothendieck constructions.

However, the paper's construction operates on category-valued presheaves. A Grothendieck institution additionally carries sentences, models, and satisfaction. The former does not automatically supply the latter.

Also, O1's pseudocoend for composing computational modules is a different categorical construction from the Grothendieck construction used to assemble indexed institutions. Similar integral notation should not obscure that distinction.

## 3. The more interesting connection: computations that change logical systems

Consider an adaptive system that uses several forms of reasoning.

Initially it might use ordinary logical constraints to describe which actions are permitted. A measurement introduces probabilistic evidence. Later, a new capability becomes available, bringing additional operations and safety requirements expressed in temporal logic.

There are now two independent kinds of change:

- Logical change: Which language, models, and satisfaction judgments are currently appropriate?
- Computational change: What evidence, resources, histories, and operations are available, and how do they compose?

Grothendieck institutions provide a natural framework for the first. O1 provides a framework for the second.

The potential combined structure would support computations such as

\\[ (i,\Sigma)\\;\rightsquigarrow\\;(j,\Gamma) \\]

where the endpoints belong to different logical regimes, while the computation also carries O1-style context and content grades.

This is especially relevant to O3–O5, where the contract calls for several semantic models, changing evidence and capabilities, and proofs about observational behavior.

The institutional component could state which propositions are meaningful and satisfied in each regime. The computational component would describe how transitions produce observations and new capabilities.

## 4. What new theorem would be needed?

The key question is whether Grothendieck assembly commutes with effect composition.

Suppose each institution in a diagram supports an O1-style computation structure with its own coherent interaction.

Can those local computation structures be assembled into a single computation structure over the Grothendieck institution?

Not automatically.

Translations between institutions preserve satisfaction, but they need not preserve computational grades, probability dependencies, resource consumption, or the interaction law \\(\tau\\).

A genuine globalization theorem would require cross-institution translations that preserve the relevant context and content structures, together with coherent comparisons for changing bases and composing effects.

The resulting obligation would be that translating a computation across logical regimes and then composing it agrees, up to the specified coherent comparison, with composing first and translating afterward.

There is also a typing obstacle: the present O1 theorem is formulated over a Set-based interface. The signature or theory category of a Grothendieck institution is not generally Set. Applying O1 there requires an appropriate base-change or generalized construction, not just substituting one category name for another.

This is a real additional research problem.

## 5. A useful direction for the programme

The natural candidate is an institution-indexed relative computation theory.

Its central question would be:

> Under what conditions can independently specified logical systems and independently specified computational effects be assembled into one coherent structure that preserves both satisfaction and computation semantics?

That would connect three bodies of mathematics:

- Grothendieck institutions: heterogeneous logic and satisfaction-preserving translation.
- Relative pseudopromonads and distributive laws: composition of effects with dependencies.
- Fibred semantics and Beck–Chevalley conditions: coherent transport across changing interfaces.

There is relevant prior work to check carefully. Diaconescu's theory already establishes globalization results concerning model amalgamation, exactness, free constructions, and theory colimits.&#x20;

[image](https://www.google.com/s2/favicons?domain=https://imar.ro\&sz=32)

Simion Stoilow Institute of Mathematics

&#x20;Those results should not be confused with O1's Beck–Chevalley and distributive-law obligations, although their interaction could be productive.



The decisive small experiment would use two institutions connected by a nontrivial logic translation, give each a concrete O1 computation structure, and check whether the translation preserves the mixed interaction and the intended satisfaction judgments. A failure would expose the missing hypothesis; a successful construction could support a general theorem.

Assessment: The connection is mathematically substantive. It is not a shortcut that automatically solves O1, and it should not displace the current programme. But it offers a principled way to extend that programme from computations with changing resources and observations to computations whose logical framework itself can change.