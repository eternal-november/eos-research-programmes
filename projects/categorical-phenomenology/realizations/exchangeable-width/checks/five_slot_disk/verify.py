"""Exact disk-certificate checker. No third-party dependencies or assertions."""
import copy
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def edge(a, b):
    return sum(x != y for x, y in zip(a, b)) == 1


def valid(path):
    require(bool(path), "Empty path")
    require(all(len(v) == 3 and len(set(v)) == 3
                and set(v) <= set(range(1, 6)) for v in path), "Invalid vertex")
    require(path[0] == path[-1] == [1, 2, 3], "Wrong basepoint")
    require(all(edge(a, b) for a, b in zip(path, path[1:])), "Invalid edge")


def triangle(a, b, c):
    return (len({tuple(a), tuple(b), tuple(c)}) == 3
            and sum(len({a[i], b[i], c[i]}) > 1 for i in range(3)) == 1
            and all(edge(x, y) for x, y in [(a, b), (b, c), (a, c)]))


def verify(data):
    current = data['initial']
    valid(current)
    counts = {}
    for move in data['elementary_moves']:
        require(move['before'] == current, "Broken certificate chain")
        a, b, kind = move['before'], move['after'], move['kind']
        valid(b)
        counts[kind] = counts.get(kind, 0) + 1
        if kind == 'square':
            require(len(a) == len(b), "Square changed length")
            changed = [i for i in range(len(a)) if a[i] != b[i]]
            require(len(changed) == 1, "Square changes multiple vertices")
            i = changed[0]
            require(0 < i < len(a) - 1, "Square changed basepoint")
            vertices = [a[i-1], a[i], a[i+1], b[i]]
            supports = [set(v[j] for v in vertices) for j in range(3)]
            require(sorted(map(len, supports)) == [1, 2, 2], "Wrong square dimensions")
            require(all(not supports[j] & supports[k]
                        for j in range(3) for k in range(j+1, 3)), "Overlapping supports")
            require(len({tuple(v) for v in vertices}) == 4, "Degenerate square")
        elif kind in ('triangle_expand', 'triangle_contract'):
            longer, shorter = (b, a) if kind == 'triangle_expand' else (a, b)
            require(len(longer) == len(shorter) + 1, "Wrong triangle length")
            require(any(longer[:i] + longer[i+1:] == shorter
                        and triangle(*longer[i-1:i+2])
                        for i in range(1, len(longer)-1)), "Invalid triangle move")
        elif kind == 'backtrack':
            require(len(a) == len(b) + 2, "Wrong backtrack length")
            require(any(a[i-1] == a[i+1] and a[:i] + a[i+2:] == b
                        for i in range(1, len(a)-1)), "Invalid backtrack")
        else:
            raise ValueError("Unknown move")
        current = b
    require(current == [[1, 2, 3]], "Certificate did not contract")
    cycle = lambda v: [v[1], v[2], v[0]]
    gamma = [[1,2,3], [4,2,3], [4,2,1], [4,3,1], [2,3,1]]
    expected = (gamma[:-1] + list(map(cycle, gamma[:-1]))
                + [cycle(cycle(v)) for v in gamma[:-1]] + [[1,2,3]])
    require(data['initial'] == expected, "Wrong C3 triple boundary")
    return counts


if __name__ == '__main__':
    data = json.loads(Path(__file__).with_name('certificate.json').read_text())
    counts = verify(data)
    bad = copy.deepcopy(data)
    bad['elementary_moves'][0]['before'][0] = [1, 1, 3]
    try:
        verify(bad)
    except ValueError:
        pass
    else:
        raise RuntimeError("Negative control was not rejected")
    print('PASS: exact C3 triple boundary contracts by', counts)
    print('19 nondegenerate 2-cells (11 squares and 8 triangles); 3 backtrack folds.')
    print('PASS: deliberately corrupted certificate rejected.')
