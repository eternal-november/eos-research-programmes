"""Finite diagnostics for Sections 4--7, using only Python's standard library.

No finite computation verifies the general pseudocoend or the ten law axioms.
Rows/positions are kept distinct. Colours form C2, so multiplication is XOR.
"""
from fractions import Fraction as Q
from itertools import product
from functools import reduce
from operator import mul

def words(alphabet, maxlen):
    return [s for n in range(maxlen + 1) for s in product(alphabet, repeat=n)]

def erase(w):
    return tuple(x for c, x in w)

def flat(w):
    return tuple((g ^ h, x) for g, inner in w for h, x in inner)

def tensor(*vs):
    return tuple(reduce(mul, xs, Q(1)) for xs in product(*vs))

def basis(n, i):
    return tuple(Q(j == i) for j in range(n))

def rank(columns):
    if not columns: return 0
    rows = list(map(list, zip(*columns)))
    r = 0
    for j in range(len(columns)):
        i = next((i for i in range(r, len(rows)) if rows[i][j]), None)
        if i is None: continue
        rows[r], rows[i] = rows[i], rows[r]
        p = rows[r][j]
        rows[r] = [Q(x, p) for x in rows[r]]
        for i in range(r + 1, len(rows)):
            q = rows[i][j]
            rows[i] = [x - q * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r

def check_cartesian_colour_erasure():
    # Pull back coloured lists along an uncoloured carrier fold, truncated at 3.
    X, G = (0, 1), (0, 1)
    lhs = words(tuple(product(G, X)), 3)
    f = lambda x: 0
    project = lambda w: (tuple((g, f(x)) for g, x in w), erase(w))
    pairs = {(w, t) for w in words(tuple(product(G, (0,))), 3)
             for t in words(X, 3) if erase(w) == tuple(map(f, t))}
    assert set(map(project, lhs)) == pairs and len(lhs) == len(pairs)
    # Naturality of restriction (erasure) with substitution including nullaries.
    inner = words(tuple(product(G, X)), 2)
    nested = words(tuple(product(G, inner)), 2)
    for w in nested:
        assert erase(flat(w)) == tuple(x for _, v in w for x in erase(v))
    return len(lhs), len(nested)

def check_c5_addresses():
    # A context row x is chosen first; the available continuations depend on x.
    pairs = ((0, 0), (1, 0), (1, 1))
    inner = words(tuple(product((0, 1), pairs)), 2)
    count = 0
    for w in words(tuple(product((0, 1), inner)), 2):
        # Flatten coloured content, then split the dependent choices.
        flat_choices = flat(w)
        l = (tuple((g, x) for g, (x, z) in flat_choices),
             tuple((g, z) for g, (x, z) in flat_choices))
        # Split within each inner word, then flatten each resulting nesting.
        outer = tuple((g, tuple((h, x) for h, (x, z) in v)) for g, v in w)
        cont  = tuple((g, tuple((h, z) for h, (x, z) in v)) for g, v in w)
        assert l == (flat(outer), flat(cont))
        count += 1
    return count

def check_directed_rows():
    e0, e1 = basis(2, 0), basis(2, 1)
    # id vs p(a,b)=(a+b,0) over the witness fold to one row.
    ident = [tensor(x,y) for x,y in product((e0,e1), repeat=2)]
    idem  = [tensor(e0,e0) for _ in ident]
    assert (rank(ident), rank(idem)) == (4,1)
    assert ident[-1] == basis(4,3) and idem[-1] == basis(4,0)
    # A source with nonconstant continuation maps at different ancestors.
    pairs = ((0,0), (1,0), (1,1))
    beta = {(0,0): e1, (1,0): e0, (1,1): (Q(1,2), Q(1,2))}
    alpha = {0: e0, 1: e1}
    columns = []
    for (x,z),(y,w) in product(pairs, repeat=2):
        ax, ay, bz, bw = alpha[x], alpha[y], beta[x,z], beta[y,w]
        # Apply native dependent transfer in each position, then the shuffle.
        before = tensor(tensor(ax,bz),tensor(ay,bw))
        after = tuple(before[((i*2+k)*2+j)*2+l]
                      for i,j,k,l in product(range(2), repeat=4))
        # First transfer inner variables for the fixed (x,y), then outer ones.
        staged = tensor(tensor(ax,ay), tensor(bz,bw))
        assert after == staged and sum(after) == 1
        columns.append(after)
    assert rank(columns) == 9
    assert tensor(alpha[0],beta[0,0]) != tensor(alpha[0],beta[1,0])
    return rank(ident), rank(idem), len(columns), rank(columns)

if __name__ == "__main__":
    c, n = check_cartesian_colour_erasure()
    s = check_c5_addresses()
    i, p, cols, r = check_directed_rows()
    print(f"Cartesianness: {c} addressed fibres; erasure/substitution: {n} nested words.")
    print(f"Flatten/split C5: {s} coloured nested dependent contexts.")
    print(f"Restriction ranks: {i} vs {p}; native Fubini: {cols} columns, rank {r}.")
