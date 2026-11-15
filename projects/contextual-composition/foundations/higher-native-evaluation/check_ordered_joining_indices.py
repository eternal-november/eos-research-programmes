"""Finite index diagnostics only; not a verification of higher coherence cells."""
from itertools import combinations_with_replacement

def maps(n, m):
    if n == 0:
        return [()]
    return list(combinations_with_replacement(range(m), n)) if m else []

def fiber_words(theta, m, words):
    # A node records its full parentheses; () is an inserted unit node.
    return tuple(tuple(words[i] for i in reversed(range(len(theta))) if theta[i] == j)
                 for j in range(m))

def leaves(word):
    if isinstance(word, int):
        return (word,)
    return sum((leaves(x) for x in word), ())

def compose(phi, theta):
    return tuple(phi[i] for i in theta)

single = pairs = triples = 0
for n in range(5):
    source = tuple(range(n))
    for m in range(5):
        for theta in maps(n, m):
            w = fiber_words(theta, m, source)
            assert leaves(tuple(reversed(w))) == tuple(reversed(source))
            single += 1
            for k in range(5):
                for phi in maps(m, k):
                    nested = fiber_words(phi, k, w)
                    direct = fiber_words(compose(phi, theta), k, source)
                    assert tuple(map(leaves, nested)) == tuple(map(leaves, direct))
                    pairs += 1
                    # Limit third-stage exhaustive cases to small interfaces.
                    if max(n, m, k) <= 3:
                        for ell in range(4):
                            for psi in maps(k, ell):
                                left = fiber_words(psi, ell, nested)
                                composite = compose(psi, compose(phi, theta))
                                right = fiber_words(composite, ell, source)
                                assert tuple(map(leaves, left)) == tuple(map(leaves, right))
                                triples += 1

# Explicit guard against pretending every image unit is the target unit literally.
uneven = fiber_words((0, 0), 2, ((), ()))
assert uneven == (((), ()), ())
assert uneven != ((), ())
assert all(leaves(x) == () for x in uneven)
assert maps(1, 0) == []
print(f"PASS: {single} maps; {pairs} composable pairs; {triples} small triples.")
print("Uneven unit tuple retained; no nonempty-to-empty map admitted.")
print("These checks erase structural cells and do not certify perturbation coherence.")
