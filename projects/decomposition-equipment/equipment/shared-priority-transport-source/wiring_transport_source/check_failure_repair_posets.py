"""Reproduce the finite checks in failure_repair_theorem.md; Python stdlib only."""
from itertools import combinations, permutations, product
from math import comb


def main():
    count = 0
    fixed_count = 0
    for n in range(2, 5):
        pairs = list(combinations(range(n), 2))
        perms = list(permutations(range(n)))
        for mask in range(1 << len(pairs)):
            edges = [p for k, p in enumerate(pairs) if mask >> k & 1]
            reach = [[False] * n for _ in range(n)]
            for i, j in edges:
                reach[i][j] = True
            for k in range(n):
                for i in range(n):
                    for j in range(n):
                        reach[i][j] |= reach[i][k] and reach[k][j]
            extensions = [p for p in perms if all(p.index(i) < p.index(j) for i, j in edges)]
            for roles in product(range(2), repeat=n):
                criterion = all(reach[i][j] or reach[j][i] or roles[i] == roles[j] for i, j in pairs)
                invariant = len({tuple(roles[i] for i in p) for p in extensions}) == 1
                assert criterion == invariant, (n, edges, roles)
                count += 1
                for bits in product(range(2), repeat=n):
                    accepted = True
                    for i, j in pairs:
                        if reach[i][j] or reach[j][i] or roles[i] == roles[j]:
                            continue
                        pred = {v for v in range(n) if reach[v][i] or reach[v][j]}
                        succ = {v for v in range(n) if reach[i][v] or reach[j][v]}
                        lower = len(pred) + 1
                        upper = n - len(succ) - 1
                        if any(bits[k - 1] != bits[k] for k in range(lower, upper + 1)):
                            accepted = False
                    vectors = set()
                    for order in extensions:
                        vector = [0, 0]
                        for rank, module in enumerate(order):
                            vector[roles[module]] ^= bits[rank]
                        vectors.add(tuple(vector))
                    assert accepted == (len(vectors) == 1), (n, edges, roles, bits)
                    fixed_count += 1
        summation = sum(comb(n, k) / (2**n) / comb(n, k) for k in range(n + 1))
        assert summation == (n + 1) / 2**n
        print(f'n={n}: average success bound={summation}')
    assert count == 1096
    print(f'PASS: {count} poset/role fixtures; {fixed_count} fixed-payload fixtures')


if __name__ == '__main__':
    main()
