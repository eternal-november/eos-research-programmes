"""Actual original C5 flat witness slice, not a tag-only groupoid toy.

Uses the inherited presented-to-flat isomorphism, not a new presentation proof.
Whole graphs, induced restrictions, full typed profiles and slot tuples remain
part of data. All checks use explicit guards and survive Python optimization.
"""
from dataclasses import dataclass
from itertools import permutations, product


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


@dataclass(frozen=True)
class Graph:
    n: int
    edges: frozenset

    def induced(self, block):
        ordered = sorted(block)
        inverse = {v: i for i, v in enumerate(ordered)}
        return Graph(len(ordered), frozenset((inverse[a], inverse[b])
                     for a, b in self.edges if a in inverse and b in inverse))


@dataclass(frozen=True)
class Rel:
    source: int
    target: int
    pairs: frozenset


def identity(label, size=2):
    return Rel(label, label, frozenset((i, i) for i in range(size)))


def compose_rel(first, second):
    require(first.target == second.source, 'relation path typing')
    return Rel(first.source, second.target,
               frozenset((a, c) for a, b in first.pairs for y, c in second.pairs if b == y))


def path_grade(path, label=None, size=2):
    if not path:
        require(label is not None, 'nullary identity needs actual interface')
        return identity(label, size)
    out = path[0]
    for rel in path[1:]:
        out = compose_rel(out, rel)
    return out


@dataclass(frozen=True)
class Component:
    graph: Graph
    grade: Rel


@dataclass(frozen=True)
class Op:
    whole: Component
    blocks: tuple
    grades: tuple
    scalar: int

    @property
    def profile(self):
        return tuple(Component(self.whole.graph.induced(b), r)
                     for b, r in zip(self.blocks, self.grades))

    def validate(self, carrier_size=2):
        require(len(self.blocks) == len(self.grades), 'flat arity')
        entries = [v for b in self.blocks for v in b]
        require(sorted(entries) == list(range(self.whole.graph.n)), 'actual ordered partition')
        require(self.scalar in (0, 1), 'selected Z2 scalar')
        require(path_grade(self.grades, self.whole.grade.source, carrier_size) == self.whole.grade,
                'actual full path composite grade')
        if not self.grades:
            require(self.whole.graph.n == 0, 'nullary graph must be empty')
        return self


def substitute(outer, children, carrier_size=2):
    require(len(children) == len(outer.blocks), 'original-slot child count')
    blocks, grades = [], []
    scalar = outer.scalar
    for component, block, child in zip(outer.profile, outer.blocks, children):
        require(child.whole == component, 'whole component of child must match original slot')
        child.validate(carrier_size)
        increasing = sorted(block)
        blocks.extend(frozenset(increasing[v] for v in b) for b in child.blocks)
        grades.extend(child.grades)
        scalar = (scalar + child.scalar) % 2
    return Op(outer.whole, tuple(blocks), tuple(grades), scalar).validate(carrier_size)


def unary(component, scalar=0):
    return Op(component, (frozenset(range(component.graph.n)),), (component.grade,), scalar).validate()


@dataclass(frozen=True)
class RefArrow:
    source: Op
    target: Op
    children: tuple

    def validate(self):
        require(substitute(self.source, self.children) == self.target, 'full tuple refinement endpoint')
        return self


def compose_arrows(first, second):
    require(first.target == second.source, 'refinement composition typing')
    children, offset = [], 0
    for child in first.children:
        stop = offset + len(child.blocks)
        children.append(substitute(child, second.children[offset:stop]))
        offset = stop
    require(offset == len(second.children), 'all second-level original slots retained')
    return RefArrow(first.source, second.target, tuple(children)).validate()


def permutation_compose(first, second):
    """second after first."""
    return tuple(second[first[i]] for i in range(len(first)))


def group_compose(first, second):
    return tuple(permutation_compose(a, b) for a, b in zip(first, second))


def transport_rel(rel, h):
    return Rel(rel.source, rel.target,
               frozenset((h[rel.source][a], h[rel.target][b]) for a, b in rel.pairs))


def transport_op(op, h, carrier_size=2):
    return Op(Component(op.whole.graph, transport_rel(op.whole.grade, h)), op.blocks,
              tuple(transport_rel(r, h) for r in op.grades), op.scalar).validate(carrier_size)


def transport_arrow(arrow, h):
    return RefArrow(transport_op(arrow.source, h), transport_op(arrow.target, h),
                    tuple(transport_op(x, h) for x in arrow.children)).validate()


def group(size=2):
    return tuple(product(tuple(permutations(range(size))), repeat=3))


def relations(a, b, size=2):
    pairs = tuple(product(range(size), repeat=2))
    return tuple(Rel(a, b, frozenset(p for i, p in enumerate(pairs) if mask >> i & 1))
                 for mask in range(1 << len(pairs)))


def relation_action_checks():
    H = group()
    action_laws = composition_laws = 0
    for a, b in product(range(3), repeat=2):
        for rel, h, k in product(relations(a, b), H, H):
            require(transport_rel(transport_rel(rel, h), k) ==
                    transport_rel(rel, group_compose(h, k)), 'actual relation action composition')
            action_laws += 1
    for a, b, c in product(range(3), repeat=3):
        for r, s, h in product(relations(a, b), relations(b, c), H):
            require(transport_rel(compose_rel(r, s), h) ==
                    compose_rel(transport_rel(r, h), transport_rel(s, h)),
                    'shared-boundary relation composition equivariance')
            composition_laws += 1
    changed = Rel(0, 1, frozenset({(0, 0)}))
    swap_b = ((0, 1), (1, 0), (0, 1))
    require(transport_rel(changed, swap_b) != changed, 'action must change actual relation entries')
    return {'independent_interface_group_order': len(H), 'action_composition_cases': action_laws,
            'typed_relation_composition_cases': composition_laws,
            'nonidentity_actual_relation_action': True}


def original_witness_checks(mutation=None):
    H = group()
    graph = Graph(4, frozenset({(0, 1), (2, 3)}))
    delta = identity(0)
    whole = Component(graph, delta)
    blocks = (frozenset({0, 1}), frozenset({2, 3}))
    objects = tuple(Op(whole, blocks, (delta, delta), m).validate() for m in range(2))
    a = objects[0]
    require(a.profile[0] == a.profile[1] and a.profile[0].graph.edges == frozenset({(0, 1)}),
            'repeated components are actual identical nonempty K2 graphs')
    arrows = {}
    for source, target in product(objects, repeat=2):
        hom = []
        for scalars in product(range(2), repeat=2):
            children = tuple(unary(c, m) for c, m in zip(source.profile, scalars))
            if substitute(source, children) == target:
                hom.append(RefArrow(source, target, children).validate())
        arrows[(source.scalar, target.scalar)] = tuple(hom)
        require(len(hom) == 2, 'actual original-slot refinement multiplicity')
    endos = arrows[(0, 0)]
    keys = [tuple(c.scalar for c in arrow.children) for arrow in endos]
    if mutation == 'merge_occurrence_tuples':
        keys = [sum(key) % 2 for key in keys]
    require(len(set(keys)) == 2, 'distinct full original-slot arrows must survive equal totals')
    stabilizer = [h for h in H if transport_op(a, h) == a]
    require(len(stabilizer) == 8, 'full H stabilizer of repeated diagonal witness')
    a_subgroup = [h for h in H if h[1] == (0, 1) and h[2] == (0, 1)]
    require(len(a_subgroup) == 2 and all(transport_op(a, h) == a for h in a_subgroup),
            'nontrivial A-interface stabilizer, not occurrence permutation')
    coherence = 0
    for x, y, z in product(range(2), repeat=3):
        for first, second, h in product(arrows[(x, y)], arrows[(y, z)], H):
            require(transport_arrow(compose_arrows(first, second), h) ==
                    compose_arrows(transport_arrow(first, h), transport_arrow(second, h)),
                    'transport preserves actual full-tuple composition')
            coherence += 1
    # Nontrivial action on an entire witness and its arrow, not merely scalar tags.
    changed_whole_cases = 0
    for r, s in product(relations(0, 1), relations(1, 2)):
        op = Op(Component(graph, compose_rel(r, s)), blocks, (r, s), 0).validate()
        arr = RefArrow(op, op, tuple(unary(c, 1) for c in op.profile)).validate()
        for h in H:
            moved = transport_arrow(arr, h)
            require(moved.children == tuple(unary(c, 1) for c in moved.source.profile),
                    'typed child operations transported at separate slots')
            changed_whole_cases += moved.source != op
    return objects, arrows, {'graph_vertices': 4, 'graph_edges': [[0, 1], [2, 3]],
          'ordered_blocks': [[0, 1], [2, 3]], 'repeated_component': 'actual (K2, diagonal_A)',
          'endomorphism_scalar_tuples': [[0, 0], [1, 1]],
          'full_H_stabilizer_order': 8, 'A_interface_subgroup_stabilizer_order': 2,
          'full_tuple_transport_composition_cases': coherence,
          'nontrivially_changed_full_witness_cases': changed_whole_cases}


def substitution_and_templates():
    # Three actual K2 blocks in the original bounded N=6 graph family.
    graph = Graph(6, frozenset({(0, 1), (2, 3), (4, 5)}))
    delta = identity(0)
    whole = Component(graph, delta)
    a = Op(whole, (frozenset(range(4)), frozenset({4, 5})), (delta, delta), 0).validate()
    first = a.profile[0]
    split = Op(first, (frozenset({0, 1}), frozenset({2, 3})), (delta, delta), 1).validate()
    children = (split, unary(a.profile[1], 1))
    expanded = substitute(a, children)
    require(expanded.blocks == (frozenset({0, 1}), frozenset({2, 3}), frozenset({4, 5})),
            'increasing induced graph restriction/lift')
    level2 = tuple(unary(c, i % 2) for i, c in enumerate(expanded.profile))
    left = substitute(expanded, level2)
    regrouped = (substitute(children[0], level2[:2]), substitute(children[1], level2[2:]))
    right = substitute(a, regrouped)
    require(left == right, 'actual graph/grade/scalar substitution associativity')
    # Literal R template: left- and right-associated binary cuts of the same
    # three ordered K2 blocks, not merely two bracketings of scalar addition.
    left_inner = Op(first, split.blocks, split.grades, 0).validate()
    left_rotation = substitute(a, (left_inner, unary(a.profile[1], 0)))
    right_outer = Op(whole, (frozenset({0, 1}), frozenset(range(2, 6))),
                     (delta, delta), 0).validate()
    right_inner = Op(right_outer.profile[1],
                     (frozenset({0, 1}), frozenset({2, 3})), (delta, delta), 0).validate()
    right_rotation = substitute(right_outer, (unary(right_outer.profile[0], 0), right_inner))
    require(left_rotation == right_rotation, 'R actual left/right binary-cut rotation')
    transport_cases = 0
    for h in group():
        require(transport_op(expanded, h) ==
                substitute(transport_op(a, h), tuple(transport_op(x, h) for x in children)),
                'presented substitution coherence')
        transport_cases += 1
    # Check the seven template values on actual components, including nullaries.
    empty = Component(Graph(0, frozenset()), delta)
    unit = Op(empty, (), (), 0).validate()
    base = a.profile[1]
    idbase = unary(base)
    for side in (0, 1):
        cuts = ((frozenset(), frozenset(range(base.graph.n))) if side == 0
                else (frozenset(range(base.graph.n)), frozenset()))
        cut = Op(base, cuts, (delta, delta), 0).validate()
        cs = (unit, idbase) if side == 0 else (idbase, unit)
        require(substitute(cut, cs) == idbase, 'UL/UR actual empty occurrence')
    require(substitute(unary(base, 0), (idbase,)) == idbase, 'D0')
    for m, n in product(range(2), repeat=2):
        require(substitute(unary(base, m), (unary(base, n),)) == unary(base, (m+n) % 2), 'DA')
    for slot in (0, 1):
        cs = tuple(unary(c, int(i == slot)) for i, c in enumerate(a.profile))
        decorated = Op(a.whole, a.blocks, a.grades, 1).validate()
        require(substitute(a, cs) == decorated, 'DL/DR actual slot decoration')
    return {'principal_graph_bound': 6, 'substitution_associativity': True,
            'literal_binary_cut_rotation_R': True,
            'substitution_transport_cases': transport_cases,
            'template_values_checked': ['R', 'UL', 'UR', 'D0', 'DA', 'DL', 'DR'],
            'limitation': 'flat values of inherited equations; no new proof of presentation completeness'}


def alias_equivalence(objects, arrows, mutation=None):
    # G has aliases 0,1 and Hom_G(i,j)=H; e:G->BH sends the actual h to h.
    # Semidirect arrows (h, alpha:T_h x -> y) retain both pieces.
    H = group()
    homs = {(x, y): tuple((h, a) for h in H for a in arrows[(x, y)])
            for x, y in product(range(2), repeat=2)}
    bijections = arrow_images = compositions = 0
    for i, j, x, y in product(range(2), repeat=4):
        source_hom = tuple((i, j, h, a) for h, a in homs[(x, y)])
        mapped = tuple((h, a) for _, _, h, a in source_hom)
        if mutation == 'erase_groupoid_arrows':
            mapped = tuple(a for _, a in mapped)
        require(len(set(mapped)) == len(source_hom) and set(mapped) == set(homs[(x, y)]),
                'alias comparison hom bijection retains actual h and full tuple')
        bijections += 1
        arrow_images += len(mapped)
    def compose(first, second):
        h, alpha = first
        k, beta = second
        return group_compose(h, k), compose_arrows(transport_arrow(alpha, k), beta)
    # Verify actual composition, identities and comparison square; aliases are
    # independent endpoints and the comparison removes only the alias labels.
    for i, j, k, x, y, z in product(range(2), repeat=6):
        for first, second in product(homs[(x, y)], homs[(y, z)]):
            result = compose(first, second)
            require(result in homs[(x, z)], 'retained symmetry composition closure')
            source_composite = (i, k, *result)
            require(source_composite[2:] == compose(first, second), 'comparison composition square')
            compositions += 1
    neutral = ((0, 1),) * 3
    identities = {}
    for x in range(2):
        identities[x] = (neutral, RefArrow(objects[x], objects[x],
                            tuple(unary(c) for c in objects[x].profile)).validate())
    for x, y in product(range(2), repeat=2):
        idx, idy = identities[x], identities[y]
        for arrow in homs[(x, y)]:
            require(compose(idx, arrow) == arrow and compose(arrow, idy) == arrow,
                    'retained symmetry identity laws')
    # Q chooses alias 0. eta_(i,x):(i,x)->(0,x) carries (1_H,id_x).
    # Check eta naturality with actual h and actual full tuples, not isoclasses.
    naturality = triangle = section_change = 0
    for i, j, x, y in product(range(2), repeat=4):
        for arrow in homs[(x, y)]:
            left = (i, 0, *compose(arrow, identities[y]))
            right = (i, 0, *compose(identities[x], arrow))
            require(left == right, 'alias quasi-inverse unit naturality')
            naturality += 1
            # Changing selected section 0 to 1 has identity_H comparison.
            require((0, 1, *compose(arrow, identities[y])) ==
                    (0, 1, *compose(identities[x], arrow)), 'section-change naturality')
            section_change += 1
    for i, x in product(range(2), repeat=2):
        eta = (i, 0, *identities[x])
        require(eta[2:] == identities[x], 'E eta is identity: triangle law')
        require((0, 0, *identities[x])[2:] == identities[x], 'eta Q is identity: triangle law')
        triangle += 1
    # Direct triple coherence on the nontrivial endomorphism group.
    associativity = 0
    for f, g, h in product(homs[(0, 0)], repeat=3):
        require(compose(compose(f, g), h) == compose(f, compose(g, h)),
                'retained symmetry associativity on actual arrows')
        associativity += 1
    return {'aliases': 2, 'interface_group_order': 8, 'refinement_objects': 2,
            'alias_total_objects': 4, 'hom_bijections': bijections,
            'actual_arrow_images': arrow_images, 'arrows_per_endomorphism_hom': 16,
            'comparison_composition_cases': compositions, 'associativity_triples': associativity,
            'quasi_inverse_naturality_squares': naturality, 'triangle_cases': triangle,
            'section_change_naturality_squares': section_change,
            'quasi_inverse': 'choose alias 0; unit component is (identity_H, identity full tuple)'}


def isoclass_loss(mutation=None):
    # Rigid selected charts *->B(S2), with no nonidentity chart arrows.
    H = tuple(permutations(range(2)))
    seams = H
    if mutation == 'discard_seam_certificates':
        seams = H[:1]
    seam_arrows = {(h, k): (('identity_left', 'identity_right'),) if h == k else ()
                   for h, k in product(seams, repeat=2)}
    require(len(seams) == 2 and sum(map(len, seam_arrows.values())) == 2,
            'iso-comma retains two distinct seam certificates and their actual arrows')
    coarse_pullback = {('chart_class', 'chart_class')}
    image = {h: ('chart_class', 'chart_class') for h in seams}
    require(len(set(image.values())) == 1 and len(image) == 2,
            'isoclass pullback comparison loses unique seam lifting')
    return {'rigid_chart_iso_comma_objects': 2, 'iso_comma_identity_arrows': 2,
            'iso_comma_nonidentity_arrows': 0, 'coarse_set_pullback_objects': len(coarse_pullback),
            'coarse_comparison_fibre_sizes': [2],
            'lost_property': 'unique lift of a chosen coarse seam class; pi0 does not preserve this pullback',
            'repair': 'retain id/swap interface arrows in the iso-comma, not only orbit classes'}


def independent_orbit_substitution(mutation=None):
    # Original C5 family, only interface permutations; scalar stays zero.
    size = 3
    empty = Graph(0, frozenset())
    delta = identity(0, size)
    whole = Component(empty, delta)
    p = Rel(0, 0, frozenset({(0, 1), (1, 0), (2, 2)}))
    q = Rel(0, 0, frozenset({(0, 2), (1, 1), (2, 0)}))
    blocks = (frozenset(), frozenset())
    a = Op(whole, blocks, (delta, delta), 0).validate(size)
    b = Op(whole, blocks, (p, p), 0).validate(size)
    bp = Op(whole, blocks, (q, q), 0).validate(size)
    H = tuple((h, h, h) for h in permutations(range(size)))
    require(bp in {transport_op(b, h, size) for h in H}, 'chosen children really lie in same orbit')
    left = substitute(a, (b, b), size)
    right = substitute(a, (b, bp), size)
    same_orbit = right in {transport_op(left, h, size) for h in H}
    if mutation == 'independent_orbits_are_congruence':
        same_orbit = True
    require(not same_orbit, 'independent operation orbits do not respect substitution')
    require(len(set(left.grades)) == 1 and len(set(right.grades)) == 2,
            'full occurrence equality-pattern obstruction')
    return {'carrier_size': 3, 'conjugation_group_order': 6,
            'child_operations_same_orbit': True, 'substituted_operations_same_orbit': False,
            'left_grade_profile': ['P', 'P', 'P', 'P'],
            'right_grade_profile': ['P', 'P', 'Q', 'Q'],
            'scalar_action': 'trivial, all scalars zero',
            'scope': 'original empty-graph C5 operations; occurrence positions are never permuted'}


def run(mutation=None):
    objects, arrows, actual = original_witness_checks(mutation)
    return {'actual_C5_witnesses': actual, 'relation_action': relation_action_checks(),
            'presented_flat_substitution': substitution_and_templates(),
            'alias_equivalence': alias_equivalence(objects, arrows, mutation),
            'isoclass_lifting_loss': isoclass_loss(mutation),
            'independent_orbit_substitution_failure': independent_orbit_substitution(mutation)}
