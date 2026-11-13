# Terminal restriction retracts force old cut equalities

Author proof submitted for independent review on 25 October 2026. This is a bounded obstruction to the paired-equation target, not completion of the central theorem. It uses actual cartesian restrictions and nonidentity boundary cells; it is not a finite-state or generic congruence argument.

## Statement with the intended comparison fixed

Let C be a typed witness calculus with distinct parallel cells a,b:(H1,...,Hn)->W, n>=1, all its displayed interfaces equal to an object o. Suppose a map of C into a virtual equipment E sends o to the one-point finite set 1, and E has the finite functions, chosen restrictions and ordinary virtual-cell substitution needed below. Let A0,...,An be any nonempty finite sets. Define the newly restricted horizontal components

    Ri = Hi[!_(i-1),!_i] : A_(i-1) -> A_i,
    T  = W[!_0,!_n] : A0 -> An.

Write chi_i:Ri -> Hi and chi:T -> W for their cartesian cells, with the indicated terminal-map boundaries. Define a^A and b^A by the UNIQUE factorizations

    chi . a^A = a[chi_1,...,chi_n],
    chi . b^A = b[chi_1,...,chi_n].                    (1)

These are actual cells in E, not arbitrary assumed semantic maps.

Theorem. Any substitution-stable equality quotient of E in which a^A=b^A also has a=b. More generally the map a -> a^A on the displayed parallel cell fibre is injective before quotient and has an explicitly given retraction after choosing one point in each Ai. In particular, no quotient imposing a^A=b^A can preserve an intended old congruence R for which a and b remain unequal. Here R is specified BEFORE completion; defining R afterwards to include the forced equality would change the conservation target.

No invertibility, injectivity, or equal-fibre hypothesis on the terminal maps is needed. Thus nontrivial balanced covers do not avoid this obstruction.

## A frozen preequipment reference congruence

The stronger conservation reading can be made noncircular by fixing the following preequipment presentation BEFORE universal completion. Start with the old C5 generators and equations. Adjoin distinct formal horizontal names R1,...,Rn,T, unary cells chi_i:Ri->Hi and chi:T->W with the terminal boundaries, and two globular cells x,y:(R1,...,Rn)->T. Impose

    chi.x = a[chi_i],    chi.y = b[chi_i],    x=y.

This is only a presented virtual double category with ordinary typed substitution. NO chi_i or chi is yet declared cartesian, and no section/return cell oldHi->Ri is present. The old congruence remains exactly the original C5 congruence on old full profiles.

Proof of the last assertion: no nonidentity generator has output Ri. Consequently every term with output Ri is an identity term with the SAME Ri leaf (up to harmless unary identity composition); in particular it cannot have an all-old frontier. Every use of x or y requires these Ri leaves. Every use of chi_i introduces one such leaf, and every use of chi after x or y retains them. Thus a cell with all-old frontier and old output can contain none of the new generators. An equation involving a new generator likewise cannot be instantiated in an all-old profile: its required Ri leaf cannot be supplied by an all-old term. Restricting the presentation to all-old profiles therefore gives exactly the original presentation and its original equations. For n>=1 this argument also handles old nullary generators; none outputs Ri. The horizontal names are kept distinct even when Ai=1 or two semantic spans happen to coincide.

Now freely require the specified chi_i and chi to be cartesian with those Ri,T as their chosen restrictions. The beta/eta operations adjoin the beta_i used below. The existing equation x=y and the two displayed comparison equations then force a=b. Thus cartesian saturation has a concrete extra cost on a reference quotient whose old conservativity has already been proved. We do not move the section cells into the preequipment reference and then pretend their ordinary contextual consequences were newly caused by completion.

This marked-existing-restriction presentation is distinct from the conservative free completion that adjoins FRESH restriction objects without marking arbitrary old cells cartesian. The no-go identifies precisely why a quotient/descent theorem needs an additional compatibility hypothesis for such markings.

## Proof on actual witnesses

Choose sections s_i:1->Ai. Cartesian universality of chi_i gives a unique unary cell

    beta_i:Hi -> Ri

with boundaries s_(i-1),s_i and chi_i . beta_i = id_(Hi): both outer vertical composites !s are identities of 1. The beta_i are composable as a tuple because their middle boundary maps are the SAME chosen s_i, not independently chosen elements at repeated occurrences.

For any alpha on the restricted profile, define

    r(alpha) = chi . alpha[beta_1,...,beta_n].          (2)

Its outer boundaries are identities, so it is a cell on the old full profile. Substitution associativity and (1) give

    r(a^A)
      = a[chi_1,...,chi_n][beta_1,...,beta_n]
      = a[chi_1.beta_1,...,chi_n.beta_n]
      = a[id,...,id]
      = a.

The identical calculation gives r(b^A)=b. Applying the actual context (2) to the proposed equation proves the assertion. The argument compares arrow DATA and retains the entire original ordered profile. It does not erase which occurrence received beta_i. QED.

The same proof works in the free chosen equipment syntax: every displayed cell is built using original cells, cartesian lift constructors, identities and substitution; each equality is a universal beta law or a virtual-double-category law. Consequently no special feature or extra semantic span map is being smuggled into the obstruction.

## The paired graph and span permutation scheme

In the graph-span-globalM model, take old components whose grade is id_o. Their spans are graph spans of id_1. The above Ri has apex Ai-1 x Ai and T has apex A0 x An. The composite-source span has apex A0 x ... x An. Both a^A and b^A have the endpoint-projection map

    phi(a0,...,an)=(a0,an).

For n>=2, any permutation theta of one nontrivial middle factor is an endpoint-preserving permutation of this composite span, and phi.theta=phi. Therefore the proposed paired local scheme

    (pi,phi,m) = (pi',phi.theta,m)

for ALL output maps phi includes a^A=b^A whenever pi and pi' are the original distinct partitions and their scalars agree. The theorem then forces the OLD partition witnesses to become equal.

This shows why a criterion based only on balanced boundary fibres or liftability of theta cannot prove old-profile conservation for the v3 scheme. The equipment's section/restriction contexts can discard the retained correlation between the graph partition and the coefficient permutation. Any valid positive repair must change the explicitly stated class of quotient judgments/contexts or retain additional non-equality data; it cannot keep the same equality quotient and claim conservation by a new name.

## Arbitrarily large graph family

For every r>=3 take the ordered complete bipartite graph K_(r,r), with ordered sides U={0,...,r-1} and V={r,...,2r-1}. Both induced graphs are the edgeless ordered r-vertex graph. Let pi=(U,V) and pi'=(V,U). They are distinct parallel C5 witnesses with the SAME whole, SAME two source graphs, SAME interface path id_o,id_o, and scalar 1 in ANY finite commutative monoid M. Cross-edges are nonempty and retained. For each k>=2 set A0=A2=1 and A1={0,...,k-1}; a nontrivial middle permutation supplies theta. The terminal map A1->1 is surjective and has balanced fibres in the only possible sense at its singleton target, but the forced old equality persists.

To realize the one-point base inside the required finite multi-interface category, take K=[2], the category 0->1->2, and o=0. Its regular representation F(0)=coproduct_C K(C,0) is the singleton containing id_0. Thus the family is compatible with a three-object K and the original regular-representation embedding, not a one-object replacement of the input class.

For each r the original size bound may be any N>=2r. This gives unbounded graph sizes, nontrivial cross-edges and unbounded internal-boundary multiplicity. The two-point illustration is not the result's scope.

## Limits of the result

This theorem does NOT prove that every interesting coupled quotient is impossible. It isolates a concrete class: substitution-stable SET equality quotients that identify these cartesian terminal restrictions while intending to retain the corresponding old cells. A marked exact fragment, an equivariant context class, a groupoid-valued observation, or a quotient that INTENDS the old equality may behave differently and requires its own positive theorem. In particular, calling a^A and b^A isomorphic rather than equal still requires an honest analysis of whether old discrete cut data acquire new isomorphisms.
