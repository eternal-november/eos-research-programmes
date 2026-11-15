"""Exact finite diagnostics for the augmented-vector native grade model.

All arithmetic is Fraction arithmetic. The matrices implement finite kernels,
pullbacks and their induced maps; they are not a proof assistant or a physical
resource interpretation. Augmented-vector limits can lack normalized witnesses.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json


@dataclass(frozen=True)
class Mat:
    rows: int
    cols: int
    data: tuple

    def __post_init__(self):
        assert self.rows >= 0 and self.cols >= 0
        assert len(self.data) == self.rows
        assert all(len(row) == self.cols for row in self.data)
        assert all(type(x) is F for row in self.data for x in row)

    def __matmul__(self, other):
        assert self.cols == other.rows
        return matrix(self.rows, other.cols,
                      lambda i, j: sum((self.data[i][k] * other.data[k][j]
                                        for k in range(self.cols)), F(0)))

    def __neg__(self):
        return matrix(self.rows, self.cols, lambda i, j: -self.data[i][j])

    def __sub__(self, other):
        assert (self.rows, self.cols) == (other.rows, other.cols)
        return matrix(self.rows, self.cols, lambda i, j: self.data[i][j] - other.data[i][j])


def matrix(rows, cols, entry):
    return Mat(rows, cols, tuple(tuple(F(entry(i, j)) for j in range(cols)) for i in range(rows)))


def rows(values, cols=None):
    values = tuple(tuple(F(x) for x in row) for row in values)
    width = len(values[0]) if values else cols
    assert width is not None
    return Mat(len(values), width, values)


def identity(n):
    return matrix(n, n, lambda i, j: int(i == j))


def hstack(*items):
    assert items and all(item.rows == items[0].rows for item in items)
    return rows(tuple(sum((item.data[i] for item in items), ())
                      for i in range(items[0].rows)), sum(item.cols for item in items))


def vstack(*items):
    assert items and all(item.cols == items[0].cols for item in items)
    return rows(sum((item.data for item in items), ()), items[0].cols)


def slice_rows(item, start, stop):
    return rows(item.data[start:stop], item.cols)


def kron(a, b):
    return matrix(a.rows * b.rows, a.cols * b.cols,
                  lambda i, j: a.data[i // b.rows][j // b.cols]
                  * b.data[i % b.rows][j % b.cols])


def rref(item):
    table = [list(row) for row in item.data]
    pivots = []
    pivot_row = 0
    for col in range(item.cols):
        candidate = next((i for i in range(pivot_row, item.rows) if table[i][col]), None)
        if candidate is None:
            continue
        table[pivot_row], table[candidate] = table[candidate], table[pivot_row]
        scalar = table[pivot_row][col]
        table[pivot_row] = [x / scalar for x in table[pivot_row]]
        for i in range(item.rows):
            if i != pivot_row and table[i][col]:
                scalar = table[i][col]
                table[i] = [x - scalar * y for x, y in zip(table[i], table[pivot_row])]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == item.rows:
            break
    return rows(table, item.cols), tuple(pivots)


def rank(item):
    return len(rref(item)[1])


def kernel(item):
    reduced, pivots = rref(item)
    free = [j for j in range(item.cols) if j not in pivots]
    pivot_rows = {pivot: i for i, pivot in enumerate(pivots)}
    basis = matrix(item.cols, len(free),
                   lambda i, j: -reduced.data[pivot_rows[i]][free[j]]
                   if i in pivot_rows else int(i == free[j]))
    assert item @ basis == matrix(item.rows, len(free), lambda i, j: 0)
    assert rank(basis) == len(free)
    return basis


def factor(inclusion, image):
    """Unique exact coordinates through a full-column-rank inclusion."""
    assert inclusion.rows == image.rows and rank(inclusion) == inclusion.cols
    augmented, pivots = rref(hstack(inclusion, image))
    n = inclusion.cols
    for row in augmented.data:
        if not any(row[:n]):
            assert not any(row[n:]), "The proposed cone does not land in the limit."
    pivot_rows = {pivot: i for i, pivot in enumerate(pivots) if pivot < n}
    assert set(pivot_rows) == set(range(n))
    result = matrix(n, image.cols, lambda i, j: augmented.data[pivot_rows[i]][n+j])
    assert inclusion @ result == image
    return result


@dataclass(frozen=True)
class Aug:
    epsilon: Mat

    def __post_init__(self):
        assert self.epsilon.rows == 1

    @property
    def dim(self):
        return self.epsilon.cols


def native(source, target, arrow):
    assert (arrow.rows, arrow.cols) == (target.dim, source.dim)
    assert target.epsilon @ arrow == source.epsilon
    return arrow


I = Aug(rows([[1]]))
U = Aug(rows([[1, 0]]))
V = Aug(rows([[1, 0, 0]]))


def tensor(a, b):
    return Aug(kron(a.epsilon, b.epsilon))


@dataclass(frozen=True)
class Pullback:
    a: Aug
    b: Aug
    boundary: Aug
    f: Mat
    g: Mat
    obj: Aug
    inclusion: Mat
    left: Mat
    right: Mat


def pullback(a, b, boundary, f, g):
    native(a, boundary, f)
    native(b, boundary, g)
    inclusion = kernel(hstack(f, -g))
    left = slice_rows(inclusion, 0, a.dim)
    right = slice_rows(inclusion, a.dim, a.dim+b.dim)
    assert f @ left == g @ right
    epsilon = a.epsilon @ left
    assert epsilon == b.epsilon @ right
    obj = Aug(epsilon)
    native(obj, a, left)
    native(obj, b, right)
    return Pullback(a, b, boundary, f, g, obj, inclusion, left, right)


def joint(a, b):
    return pullback(a, b, I, a.epsilon, b.epsilon)


def induced(source, target, a, b, boundary):
    native(source.a, target.a, a)
    native(source.b, target.b, b)
    native(source.boundary, target.boundary, boundary)
    assert target.f @ a == boundary @ source.f
    assert target.g @ b == boundary @ source.g
    arrow = factor(target.inclusion, vstack(a @ source.left, b @ source.right))
    assert target.left @ arrow == a @ source.left
    assert target.right @ arrow == b @ source.right
    return native(source.obj, target.obj, arrow)


def joint_map(source, target, a, b):
    return induced(source, target, a, b, identity(1))


def printed(item):
    return [[int(x) if x.denominator == 1 else str(x) for x in row] for row in item.data]


def coefficient_products_and_maps():
    j = joint(U, U)
    assert j.obj.dim == 3
    nice_embedding = rows([[1, 0, 0], [0, 1, 0], [1, 0, 0], [0, 0, 1]])
    nice_to_kernel = factor(j.inclusion, nice_embedding)
    kernel_to_nice = factor(nice_to_kernel, identity(3))
    assert j.obj.epsilon @ nice_to_kernel == rows([[1, 0, 0]])
    ident = native(U, U, identity(2))
    erase = native(U, U, rows([[1, 0], [0, 0]]))
    shear = native(U, U, rows([[1, 0], [2, 1]]))
    unshear = native(U, U, rows([[1, 0], [-2, 1]]))
    assert ident != erase and rank(erase) == 1
    # Same raw carrier map, distinct actual native coefficient arrows.
    native_cell_1 = ((0,), ident)
    native_cell_2 = ((0,), erase)
    assert native_cell_1[0] == native_cell_2[0] and native_cell_1 != native_cell_2
    changed = joint_map(j, j, ident, erase)
    changed_nice = kernel_to_nice @ changed @ nice_to_kernel
    assert changed_nice == rows([[1, 0, 0], [0, 1, 0], [0, 0, 0]])
    assert joint_map(j, j, ident, ident) == identity(3)
    composition_cases = 0
    for a, b, c, d in product((ident, erase, shear, unshear), repeat=4):
        assert joint_map(j, j, c @ a, d @ b) == joint_map(j, j, c, d) @ joint_map(j, j, a, b)
        composition_cases += 1

    # A nontrivial two-coordinate boundary, not just the augmentation scalar.
    f = rows([[1, 0, 0], [0, 1, 0]])
    g = rows([[1, 0, 0], [0, 0, 1]])
    pb = pullback(V, V, U, f, g)
    assert pb.obj.dim == 4
    left_map = rows([[1, 0, 0], [0, 1, 0], [0, 0, 0]])
    right_map = rows([[1, 0, 0], [0, 0, 0], [0, 0, 1]])
    arrow = induced(pb, pb, left_map, right_map, identity(2))
    assert rank(arrow) == 2
    return {
        "U_epsilon": printed(U.epsilon),
        "joint_dimension": j.obj.dim,
        "kernel_basis": printed(j.inclusion),
        "nice_coordinates": "(a,b,c) -> ((a,b),(a,c))",
        "same_raw_distinct_native_maps": [printed(ident), printed(erase)],
        "induced_joint_map_in_nice_coordinates": printed(changed_nice),
        "identity_and_composition_cases": composition_cases,
        "two_coordinate_boundary_pullback_dimension": pb.obj.dim,
        "induced_boundary_map_rank": rank(arrow),
    }


def reassociation():
    ab, bc = joint(U, V), joint(V, U)
    left, right = joint(ab.obj, U), joint(U, bc.obj)
    left_projections = (ab.left @ left.left, ab.right @ left.left, left.right)
    right_projections = (right.left, bc.left @ right.right, bc.right @ right.right)
    inner_bc = factor(bc.inclusion, vstack(left_projections[1], left_projections[2]))
    associator = factor(right.inclusion, vstack(left_projections[0], inner_bc))
    inner_ab = factor(ab.inclusion, vstack(right_projections[0], right_projections[1]))
    inverse = factor(left.inclusion, vstack(inner_ab, right_projections[2]))
    native(left.obj, right.obj, associator)
    native(right.obj, left.obj, inverse)
    assert left.obj.dim == right.obj.dim == 5
    assert inverse @ associator == identity(5) and associator @ inverse == identity(5)
    assert all(p @ associator == q for p, q in zip(right_projections, left_projections))
    alpha = native(U, U, rows([[1, 0], [0, 0]]))
    beta = native(V, V, rows([[1, 0, 0], [0, 0, 0], [0, 0, 1]]))
    gamma = native(U, U, rows([[1, 0], [3, 1]]))
    left_arrow = joint_map(left, left, joint_map(ab, ab, alpha, beta), gamma)
    right_arrow = joint_map(right, right, alpha, joint_map(bc, bc, beta, gamma))
    assert associator @ left_arrow == right_arrow @ associator
    return {
        "coefficient_dimensions": [2, 3, 2],
        "three_factor_joint_dimension": 5,
        "associator": printed(associator),
        "inverse_and_native_projections_checked": True,
        "naturality_with_noninvertible_coefficient_maps": True,
    }


def dependent_tensor():
    alpha = {
        "l": native(U, U, rows([[1, 0], [0, 0]])),
        "r": native(V, U, rows([[1, 0, 0], [0, 1, 1]])),
    }
    first = {"l": U, "r": V}
    second = {("l", 0): U, ("r", 0): U, ("r", 1): I}
    target_second = {0: U, 1: I}
    beta = {
        ("l", 0): identity(2),
        ("r", 0): rows([[1, 0], [0, 0]]),
        ("r", 1): identity(1),
    }
    native_arrows = {}
    for (x, y), q in second.items():
        source = tensor(first[x], q)
        target = tensor(U, target_second[y])
        native(q, target_second[y], beta[(x, y)])
        arrow = kron(alpha[x], beta[(x, y)])
        native(source, target, arrow)
        native_arrows[(x, y)] = arrow
    # Native maps aggregate the two raw rows with y=0 by the genuine direct sum.
    merged = hstack(native_arrows[("l", 0)], native_arrows[("r", 0)])
    source_sum_epsilon = hstack(tensor(U, U).epsilon, tensor(V, U).epsilon)
    assert tensor(U, U).epsilon @ merged == source_sum_epsilon
    outer_merge_first = hstack(kron(alpha["l"], identity(2)), kron(alpha["r"], identity(2)))
    # Two normalized witnesses become identical after outer aggregation, but
    # their x-dependent continuation maps produce different native witnesses.
    from_left = matrix(10, 1, lambda i, j: int(i in (0, 1)))
    from_right = matrix(10, 1, lambda i, j: int(i in (4, 5)))
    assert source_sum_epsilon @ from_left == source_sum_epsilon @ from_right == rows([[1]])
    assert outer_merge_first @ from_left == outer_merge_first @ from_right
    assert merged @ from_left != merged @ from_right
    # Hence no single linear post-map can recover the correct composite after
    # this premature merge. Applying each continuation before merging is real.
    difference = from_left - from_right
    assert outer_merge_first @ difference == matrix(4, 1, lambda i, j: 0)
    assert merged @ difference != matrix(4, 1, lambda i, j: 0)
    triples = []
    for (x, y), q in second.items():
        for z in range(1 + int(x == "r") + y):
            r = I if z % 2 == 0 else U
            a = first[x]
            left = tensor(tensor(a, q), r)
            right = tensor(a, tensor(q, r))
            assert left == right
            gamma = identity(r.dim)
            second_arrow = beta[(x, y)]
            assert kron(kron(alpha[x], second_arrow), gamma) == kron(alpha[x], kron(second_arrow, gamma))
            # The raw associator keeps the actual dependent addressed choices.
            source_address = ((x, y), z)
            target_address = (x, (y, z))
            assert (source_address[0][0], (source_address[0][1], source_address[1])) == target_address
            triples.append((x, y, z, left.dim))
    return {
        "source_dependent_raw_rows": len(second),
        "target_rows_after_directed_merge": 2,
        "merged_actual_coefficient_matrix": printed(merged),
        "augmentation_preserved_on_each_row_and_merged_fibre": True,
        "dependent_continuations_applied_before_aggregation": True,
        "no_linear_postmap_recovers_the_premature_outer_merge": True,
        "separating_inputs_are_normalized_epsilon_one_witnesses": True,
        "three_stage_addressed_rows": triples,
        "tensor_associativity_and_native_maps_checked": True,
    }


def forward_interchanger():
    j = joint(U, U)
    source = tensor(j.obj, j.obj)
    uu = tensor(U, U)
    target = joint(uu, uu)
    component_1 = kron(j.left, j.left)
    component_2 = kron(j.right, j.right)
    comparison = factor(target.inclusion, vstack(component_1, component_2))
    native(source, target.obj, comparison)
    assert target.left @ comparison == component_1
    assert target.right @ comparison == component_2
    assert (source.dim, target.obj.dim, rank(comparison)) == (9, 7, 7)
    assert kernel(comparison).cols == 2

    # Exhibit the map in interpretable coordinates, independently of RREF basis.
    nice_j = rows([[1, 0, 0], [0, 1, 0], [1, 0, 0], [0, 0, 1]])
    j_coords = factor(j.inclusion, nice_j)
    target_nice = rows([
        [1, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0],
        [0, 0, 1, 0, 0, 0, 0],
        [0, 0, 0, 1, 0, 0, 0],
        [1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 1],
    ])
    target_coords = factor(target.inclusion, target_nice)
    target_inverse = factor(target_coords, identity(7))
    nice_comparison = target_inverse @ comparison @ kron(j_coords, j_coords)
    selected = (0, 1, 3, 4, 2, 6, 8)
    expected = matrix(7, 9, lambda i, j: int(j == selected[i]))
    assert nice_comparison == expected
    for omitted in (5, 7):
        basis_vector = matrix(9, 1, lambda i, j: int(i == omitted))
        assert nice_comparison @ basis_vector == matrix(7, 1, lambda i, j: 0)
    return {
        "source_dimension": 9,
        "target_dimension": 7,
        "rank": 7,
        "kernel_dimension": 2,
        "nice_comparison": printed(nice_comparison),
        "source_tensor_basis_order": "00,01,02,10,11,12,20,21,22",
        "retained_coordinates": ["00", "01", "10", "11", "02", "20", "22"],
        "forgotten_cross_coordinates": ["12", "21"],
        "not_invertible": True,
    }


def definitional_reindex_and_unit():
    contexts = {
        "a": ({0: U, 1: V}, {0: U}),
        "b": ({0: I}, {0: V, 1: U}),
    }
    u = {"a0": "a", "a1": "a", "b0": "b"}
    def joint_family(pair):
        first, second = pair
        # Matching public output is included; it is not inferred from grades.
        return {(x, y): joint(a, b)
                for x, a in first.items() for y, b in second.items() if x % 2 == y % 2}
    old_joint = {a: joint_family(pair) for a, pair in contexts.items()}
    after_reindex = {a: old_joint[u[a]] for a in u}
    before_reindex = {a: joint_family(contexts[u[a]]) for a in u}
    # This is a definitional pointwise reindex check, not independent evidence
    # of a general Beck-Chevalley or native public-case theorem.
    assert after_reindex == before_reindex
    unit_joint = joint(I, I)
    assert unit_joint.obj.dim == 1 and tensor(I, I) == I
    diagonal = factor(unit_joint.inclusion, rows([[1], [1]]))
    native(I, unit_joint.obj, diagonal)
    assert rank(diagonal) == 1
    # Unit coefficient arrows are uniquely identity, even when a raw map merges.
    merged = rows([[1, 1]])
    assert I.epsilon @ merged == rows([[1, 1]])
    assert native(I, I, identity(1)) == rows([[1]])
    return {
        "definitional_pointwise_reindex_cases": len(u),
        "definitional_joint_reindex_equality": True,
        "unit_coefficients_recover_raw_only_carrier_maps": True,
        "scope": "Pointwise definitional reindexing and unit coefficients only; no independent public-case test or general Beck-Chevalley verification.",
    }


def incompatible_normalized_witnesses():
    f = native(I, U, rows([[1], [0]]))
    g = native(I, U, rows([[1], [1]]))
    equalizer = kernel(f - g)
    augmentation = I.epsilon @ equalizer
    assert equalizer.cols == 0 and rank(augmentation) == 0
    # Both individual maps are legal and the raw carrier could be a singleton,
    # yet the joint coefficient equation has no epsilon=1 witness.
    return {
        "parallel_native_maps": [printed(f), printed(g)],
        "equalizer_dimension": 0,
        "no_normalized_epsilon_one_witness": True,
        "coefficient_limit_existence_is_not_admission_or_physical_availability": True,
    }


def no_functorial_group_section():
    sections = [(zero, one) for zero in (0, 2) for one in (1, 3)]
    unit_sections = [s for s in sections if s[0] == 0]
    homomorphisms = [s for s in sections if all(
        s[(a+b) % 2] == (s[a]+s[b]) % 4 for a, b in product(range(2), repeat=2))]
    assert len(sections) == 4 and len(unit_sections) == 2 and homomorphisms == []
    assert all((s[1]+s[1]) % 4 == 2 != s[0] for s in unit_sections)
    return {
        "set_sections_C4_to_C2": 4,
        "unit_preserving_sections": 2,
        "composition_preserving_sections": 0,
        "scope": "A separate exact boundary: surjective local lifting is not a coherent chosen section.",
    }


def main():
    if not __debug__:
        raise RuntimeError("Run without optimization; assertions perform the diagnostics.")
    result = {
        "status": "PASS",
        "model": "Augmented finite rational vector spaces; original augmented families retain actual coefficient maps.",
        "pullbacks_and_native_maps": coefficient_products_and_maps(),
        "native_reassociation": reassociation(),
        "dependent_tensor": dependent_tensor(),
        "forward_joint_tensor_comparison": forward_interchanger(),
        "definitional_reindex_unit": definitional_reindex_and_unit(),
        "normalized_witness_obstruction": incompatible_normalized_witnesses(),
        "chosen_lift_obstruction": no_functorial_group_section(),
        "scope": "Finite exact matrix diagnostics, not a proof assistant, a general categorical theorem, or physical resource/source certification.",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
