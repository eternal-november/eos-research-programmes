"""Check an error-free optical UART phase model. No hardware or field replay."""
from itertools import product
from pathlib import Path
import json

N = 11
MASK = (1 << N) - 1
alphabet = tuple(map(int, Path(__file__).with_name("alphabet.txt").read_text().split()))
assert len(alphabet) == len(set(alphabet)) == 84

def string_frame(x):
    bits = f"{x:07b}"
    return "0" + bits + str(bits.count("1") % 2) + "11"

def int_frame(x):
    return (x << 3) | (x.bit_count() % 2 << 2) | 3

def int_window(x, y, offset):
    return (((x << N) | y) >> (N - offset)) & MASK

frames = [string_frame(i) for i in range(128)]
ints = [int_frame(i) for i in range(128)]
assert all(int(w, 2) == v for w, v in zip(frames, ints))
all_payloads = {w:i for i, w in enumerate(frames)}
dictionary = {frames[i]: i for i in alphabet}
integer_code = {ints[i] for i in alphabet}
classes = {}
directed_aliases = []
for x, w in enumerate(frames):
    rotations = [w[s:] + w[:s] for s in range(N)]
    assert len(set(rotations)) == N
    integer_rotations = [int_window(ints[x], ints[x], s) for s in range(N)]
    assert set(map(lambda b: int(b, 2), rotations)) == set(integer_rotations)
    classes.setdefault(min(rotations), []).append(x)
    for s in range(1, N):
        if rotations[s] in all_payloads:
            directed_aliases.append((x,s,all_payloads[rotations[s]]))
assert (83,8,106) in directed_aliases
assert len(directed_aliases) == 96
assert len({a for a, _, _ in directed_aliases}) == 84
assert len(classes) == 84
assert all(len(set(alphabet).intersection(members)) == 1 for members in classes.values())

def candidates(code):
    return {frames[i] for i in code}

def spurious_count(code):
    d = candidates(code)
    return sum(
        frames[x][s:] + frames[y][:s] in d
        for x,y,s in product(code,code,range(1,N))
    )

assert spurious_count(alphabet) == 0
min_reps = [min(members) for members in classes.values()]
max_reps = [max(members) for members in classes.values()]
min_rep_spurious, max_rep_spurious = map(spurious_count,(min_reps,max_reps))
assert min_rep_spurious > 0 and max_rep_spurious > 0
marker = [i for i, w in enumerate(frames) if "110" not in w]
assert len(marker) == 44 and spurious_count(marker) == 0

# Check the first accepted frame at every visible offset of each ordered pair.
# Reference scans fixed-width bit windows without calling the string decoder.
start_cases = 0
longest = 0
for x, y, start in product(alphabet,alphabet,range(N)):
    wire = frames[x] + frames[y]
    accepted = next(pos for pos in range(start, N+1) if wire[pos:pos+N] in dictionary)
    oracle = next(pos for pos in range(start, N+1)
                  if int_window(ints[x], ints[y], pos) in integer_code)
    assert accepted == oracle == (0 if start == 0 else N)
    assert dictionary[wire[accepted:accepted+N]] == (x if start == 0 else y)
    start_cases += 1
    longest = max(longest, accepted + N - start)
assert longest == 21

# Aligned check detects any single flip; this is not a bound for wrong phase.
for x,s in product(alphabet,range(N)):
    assert (ints[x] ^ (1 << s)) not in integer_code
w = frames[0][8:] + frames[1][:8]
assert w not in dictionary and dictionary[w[:9] + "1" + w[10:]] == 96
print(json.dumps({
    "uart_symbols": len(frames),
    "primitive_rotation_classes": len(classes),
    "rotation_bound_attained": len(alphabet),
    "directed_false_repetition_offsets": len(directed_aliases),
    "symbols_with_false_repetition": len({x for x,_,_ in directed_aliases}),
    "min_representative_spurious_splices": min_rep_spurious,
    "max_representative_spurious_splices": max_rep_spurious,
    "interior_110_forbidden_alphabet": len(marker),
    "selected_splices": len(alphabet)**2 * (N-1),
    "wrong_phase_accepts": 0,
    "two_frame_phase_replays": start_cases,
    "aligned_single_flip_checks": len(alphabet)*N,
    "max_symbols_observed_through_first_accept": longest,
    "single_wrong_phase_flip_witness": {"old":0,"new":1,"shift":8,"received_payload":96},
    "synthetic_channel": True
},indent=2,sort_keys=True))
