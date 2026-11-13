#!/usr/bin/env python3
"""Exact finite certificates for the common-realization boundary.

Python standard library only. Checks use explicit exceptions, including under -O.
No numerical optimization, latent-model search, or proof of a general theorem.
"""
from fractions import Fraction as F
from itertools import combinations, product
import json


def require(test, message):
    if not test:
        raise RuntimeError(message)


def rank(matrix):
    a = [list(map(F, row)) for row in matrix]
    if not a:
        return 0
    row = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        q = a[row][col]
        a[row] = [x / q for x in a[row]]
        for i in range(len(a)):
            if i != row:
                q = a[i][col]
                a[i] = [x - q * y for x, y in zip(a[i], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def mul(a, b):
    require(bool(a) and bool(b), 'Matrices must be nonempty')
    require(all(len(row) == len(b) for row in a), 'Matrix dimensions')
    return [[sum((x * y for x, y in zip(row, column)), F(0))
             for column in zip(*b)] for row in a]


def stochastic(a):
    return all(all(x >= 0 for x in row) and sum(row) == 1 for row in a)


def deterministic_map(values, codomain_size):
    return [[F(int(j == value)) for j in range(codomain_size)]
            for value in values]


def boundary_case():
    h = [[F(x, 2) for x in row]
         for row in ((1, 1, 0, 0), (0, 1, 1, 0),
                     (0, 0, 1, 1), (1, 0, 0, 1))]
    require(stochastic(h), 'H is stochastic')
    linear_rank = rank(h)
    affine_rank = rank([[x - y for x, y in zip(row, h[0])] for row in h[1:]])
    require(linear_rank == 3, 'rank H = 3')
    require(affine_rank == 2, 'affine dimension = 2')
    require([x + y for x, y in zip(h[0], h[2])] ==
            [x + y for x, y in zip(h[1], h[3])], 'Diagonal midpoint relation')
    u = [x - y for x, y in zip(h[1], h[0])]
    v = [x - y for x, y in zip(h[3], h[0])]
    require(sum(x * y for x, y in zip(u, v)) == 0, 'Adjacent sides orthogonal')
    require(sum(x * x for x in u) == sum(x * x for x in v) > 0,
            'Adjacent sides have equal positive length')
    # Each row uniquely maximizes the sum of the two coordinates in its support.
    # These four linear functionals certify all four rows are extreme points.
    for i, row in enumerate(h):
        support = [j for j, x in enumerate(row) if x > 0]
        vals = [sum(r[j] for j in support) for r in h]
        require(vals[i] == 1 and all(vals[k] < 1 for k in range(4) if k != i),
                'Unique supporting functional for row %d' % i)
    # Positive diagonal is a fooling set: no all-positive rectangle can contain
    # two selected positions, because one of the cross positions is zero.
    fooling_set = [(i, i) for i in range(4)]
    require(all(h[i][j] > 0 for i, j in fooling_set), 'Fooling set positive')
    for (i, j), (k, ell) in combinations(fooling_set, 2):
        require(h[i][ell] == 0 or h[k][j] == 0, 'Fooling-set cross-zero')
    # A nonnegative rank-one summand has rectangular positive support. Thus this
    # certificate proves at least four summands/latent states. Identity gives 4.
    identity = deterministic_map(tuple(range(4)), 4)
    require(stochastic(identity) and mul(identity, h) == h,
            'Four-state stochastic factorization')
    # The free 4-state simplex map to the observed hull is NOT injective.
    a = [[F(1, 2), F(0), F(1, 2), F(0)]]
    b = [[F(0), F(1, 2), F(0), F(1, 2)]]
    require(a != b and mul(a, h) == mul(b, h), 'Distinct hidden mixtures identified')
    return h, {
        'linear_rank': linear_rank,
        'affine_dimension': affine_rank,
        'exposed_vertices': 4,
        'shape': 'square',
        'nonnegative_rank_lower_certificate': 'four-position fooling set',
        'nonnegative_rank_upper_certificate': 'H = I4 H',
        'nonnegative_rank': 4,
        'simplex_hull': False,
        'distinct_simplex_mixtures_have_equal_observations': True,
        'displayed_factorization_generated': True,
        'displayed_factorization_observable': False,
    }


def boolean_case():
    universe = frozenset((0, 1))
    rows = (frozenset((0,)), frozenset((1,)))
    closed = {universe}
    for mask in product((0, 1), repeat=2):
        result = universe
        for bit, row in zip(mask, rows):
            if bit:
                result = result.intersection(row)
        closed.add(result)
    expected = {frozenset(), frozenset((0,)), frozenset((1,)), universe}
    require(len(set(rows)) == 2 and closed == expected, 'Boolean closure cardinality')
    return {'distinct_rows': 2, 'intersection_closed_profiles': 4,
            'empty_intersection_is_top': sorted(universe),
            'empty_profile_present': True}


def coarse_grain_cases(h):
    records = []
    commuting_squares = 0
    for values in product(range(2), repeat=4):
        c = deterministic_map(values, 2)
        projected = mul(h, c)
        require(stochastic(c) and stochastic(projected), 'Stochastic projection')
        # A convex hull of distributions on two outputs is an interval.
        low = min(row[0] for row in projected)
        high = max(row[0] for row in projected)
        endpoints = [[low, 1 - low]] if low == high else [[low, 1 - low], [high, 1 - high]]
        if low == high:
            weights = [[F(1)] for row in projected]
        else:
            weights = [[(high - row[0]) / (high - low), (row[0] - low) / (high - low)]
                       for row in projected]
        require(stochastic(weights) and stochastic(endpoints), 'Hull simplex factors')
        require(mul(weights, endpoints) == projected, 'Projected endpoint realization')
        require(rank(projected) == len(endpoints), 'Projected rank and endpoint count')
        # Every two-stage deterministic coarse-graining has the same result as
        # its composite. This is exact matrix equality, not Monte Carlo testing.
        for second_values in product(range(2), repeat=2):
            d = deterministic_map(second_values, 2)
            require(mul(projected, d) == mul(h, mul(c, d)), 'Two-stage observation coherence')
            require(mul(weights, mul(endpoints, d)) == mul(projected, d),
                    'Realization transported through further observation')
            commuting_squares += 1
        records.append({'outcome_map': list(values), 'hull_vertices': len(endpoints),
                        'linear_rank': rank(projected)})
    # Two distinct observations coalesce in this nonconstant coarse graining.
    c = deterministic_map((0, 0, 1, 1), 2)
    g = mul(h, c)
    require(g == [[F(1), F(0)], [F(1, 2), F(1, 2)],
                  [F(0), F(1)], [F(1, 2), F(1, 2)]], 'Square-to-segment example')
    require(h[1] != h[3] and g[1] == g[3], 'Information loss under coarse-graining')
    point = mul(h, deterministic_map((0, 1, 0, 1), 2))
    require(all(row == [F(1, 2), F(1, 2)] for row in point), 'Square-to-point example')
    return {'maps_checked': len(records), 'two_stage_squares_checked': commuting_squares,
            'point_hulls': sum(r['hull_vertices'] == 1 for r in records),
            'segment_hulls': sum(r['hull_vertices'] == 2 for r in records),
            'square_to_segment_map': [0, 0, 1, 1],
            'square_to_point_map': [0, 1, 0, 1], 'records': records}



def inner_square_case(boundary):
    h = [[F(x, 12) for x in row]
         for row in ((5, 4, 3), (5, 2, 5), (3, 6, 3), (3, 4, 5))]
    require(stochastic(h), 'Inner square stochastic')
    require(rank(h) == 3, 'Inner square rank 3')
    require(rank([[x - y for x, y in zip(row, h[0])] for row in h[1:]]) == 2,
            'Inner square affine dimension 2')
    require([x + y for x, y in zip(h[0], h[3])] ==
            [x + y for x, y in zip(h[1], h[2])], 'Inner parallelogram relation')
    functionals = ((1, 0, -1), (1, -1, 0), (-1, 1, 0), (-1, 0, 1))
    for i, functional in enumerate(functionals):
        vals = [sum(x * y for x, y in zip(row, functional)) for row in h]
        require(all(vals[i] > vals[k] for k in range(4) if k != i),
                'Inner square vertex exposed')
    identity = deterministic_map(tuple(range(3)), 3)
    require(stochastic(identity) and mul(h, identity) == h,
            'Three-state stochastic realization Hinner = Hinner I3')
    for j in range(3):
        require(max(row[j] for row in h) < 1,
                'Every latent simplex vertex is outside generated hull')
    # General rank <= nonnegative rank plus this factorization gives nnrank 3.
    # An affine isomorphism of the hulls maps boundary vertices 0,1,3,2 to
    # inner vertices 0,1,2,3. Write both as affine unit squares.
    def forward(x):
        ss, tt = 2 * x[2], 2 * x[3]
        return [a + ss * (b - a) + tt * (c - a)
                for a, b, c in zip(h[0], h[1], h[2])]
    def backward(z):
        ss, tt = 6 * z[2] - F(3, 2), F(5, 2) - 6 * z[0]
        return [a + ss * (b - a) + tt * (c - a)
                for a, b, c in zip(boundary[0], boundary[1], boundary[3])]
    order = (0, 1, 3, 2)
    for boundary_index, inner_index in enumerate(order):
        require(forward(boundary[boundary_index]) == h[inner_index],
                'Affine hull map sends vertex as specified')
        require(backward(h[inner_index]) == boundary[boundary_index],
                'Inverse affine map on vertices')
    # These checks determine equality of affine maps on each entire affine hull.
    return {'linear_rank': 3, 'affine_dimension': 2, 'exposed_vertices': 4,
            'shape': 'parallelogram (affinely a square)',
            'nonnegative_rank': 3,
            'nonnegative_rank_lower_certificate': 'ordinary rank 3',
            'nonnegative_rank_upper_certificate': 'Hinner = Hinner I3',
            'displayed_factorization_generated': False,
            'displayed_factorization_observable': True,
            'all_displayed_latent_emissions_outside_generated_hull': True,
            'abstract_convex_hull_isomorphic_to_boundary_square': True,
            'boundary_to_inner_vertex_indices': list(order),
            'same_abstract_hull_different_minimum_latent_counts': [4, 3]}


def noncartesian_mixed_square():
    q_fine = {(1, 0), (0, 1)}
    c_fine = set(product((0, 1), repeat=2))
    q_coarse = {0, 1}
    c_coarse = {0, 1}
    require({x[0] for x in q_fine} == q_coarse, 'Restriction of observed rows')
    require({x[0] for x in c_fine} == c_coarse, 'Restriction of completed profiles')
    require(len(q_fine) == len(q_coarse), 'Observed restriction is bijective')
    # Horizontal arrows include observed rows into the completion; vertical
    # arrows restrict the test coordinate. Both composites send x to x[0].
    for x in q_fine:
        require(x in c_fine and x[0] in q_coarse and x[0] in c_coarse,
                'Mixed square well-defined')
    pullback = {(q, c) for q in q_coarse for c in c_fine if q == c[0]}
    image = {(x[0], x) for x in q_fine}
    missing = pullback - image
    require(image.issubset(pullback), 'Commuting-square induced map')
    require(len(pullback) == 4 and len(image) == 2 and len(missing) == 2,
            'Mixed square is not a pullback')
    require(missing == {(0, (0, 0)), (1, (1, 1))}, 'Exact missing pullback witnesses')
    return {'fine_rows': sorted(map(list, q_fine)),
            'fine_completed_profiles': sorted(map(list, c_fine)),
            'coarse_rows_equal_completed_profiles': [0, 1],
            'observed_restriction_bijective': True,
            'commutes': True, 'is_pullback': False,
            'pullback_witnesses': [[q, list(c)] for q, c in sorted(pullback)],
            'induced_image_witnesses': [[q, list(c)] for q, c in sorted(image)],
            'missing_witnesses': [[q, list(c)] for q, c in sorted(missing)]}


def main():
    h, boundary = boundary_case()
    result = {'status': 'pass', 'arithmetic': 'exact rational',
              'stochastic_boundary': boundary,
              'inner_square_comparison': inner_square_case(h),
              'noncartesian_mixed_square': noncartesian_mixed_square(),
              'boolean_comparison': boolean_case(),
              'observation_changes': coarse_grain_cases(h),
              'scope': 'finite certificates; general claims require the accompanying proofs'}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
