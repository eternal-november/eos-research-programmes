"""Exact finite diagnostics; not certification of categorical theorems."""
from fractions import Fraction as F
from itertools import product, permutations, combinations
from collections import defaultdict

def push(law, f):
    result = defaultdict(F)
    for w, p in law.items(): result[f(w)] += p
    return dict(result)

bits = list(product(range(2), repeat=2))
diag = {w: F(w[0] == w[1], 2) for w in bits}
anti = {w: F(w[0] != w[1], 2) for w in bits}
assert diag != anti
mix = {w: (diag[w] + anti[w])/2 for w in bits}
assert all(p == F(1,4) for p in mix.values())
# The target averaged choice exists, but equals neither source local control.
assert mix != diag and mix != anti
for law in (diag, anti, mix):
    for i in range(2): assert push(law, lambda w: w[i]) == {0:F(1,2),1:F(1,2)}
print('PASS: pointwise section descent fails although flattened mixture is admitted.')

mu = {0:F(1,2), 1:F(1,2), 2:F(0)}
r = {0:0, 1:0, 2:1}; s = {0:'*',1:'*'}
assert push(push(mu, r.__getitem__), s.__getitem__) == push(mu, lambda w:s[r[w]])
# Direct and iterated retained implementation keep every raw index, including 2.
Cfinal = {'*': ('actual final coefficient',)}
retained_direct = {w:Cfinal[s[r[w]]] for w in mu}
retained_iterated = {w:{v:Cfinal[s[v]] for v in r.values()}[r[w]] for w in mu}
assert retained_direct == retained_iterated and 2 in retained_direct
print('PASS: finite retained dilation composes, without deleting zero raw points.')

# All raw paths remain, even at zero prefix; two dependent graft bracketings.
second = {0:{0:F(1),1:F(0)},1:{0:F(0),1:F(1)},2:{0:F(1,2),1:F(1,2)}}
third = {(w,z):{0:F(1,4),1:F(3,4),2:F(0)} for w in mu for z in second[w]}
left = {}; right = {}
for w,p in mu.items():
    for z,q in second[w].items():
        for v,t in third[w,z].items():
            left[((w,z),v)] = (p*q)*t
            right[(w,(z,v))] = p*(q*t)
assert sum(left.values()) == 1
assert all(p == right[(w,(z,v))] for ((w,z),v),p in left.items())
assert len(left) == 18 and sum(p == 0 for p in left.values()) == 14
# Every five-factor bracketing evaluates to same exact scalar and address.
for values in product([F(0),F(1,2),F(1)], repeat=5):
    a,b,c,d,e=values
    assert ((((a*b)*c)*d)*e) == a*(b*(c*(d*e)))
print('PASS: 18 raw graft leaves, 14 zero leaves; exact mass/cut rebracketing.')

I = set(range(3)); W = list(product(range(2), repeat=3))
subsets = [set(J) for n in range(4) for J in combinations(I,n)]
def record(w,J): return (w, tuple(w[i] for i in sorted(J)))
def reveal(state,J): return record(state[0],J)
def rawmap(w): return (0,w[1],1-w[2])
def transport(state,J): return record(rawmap(state[0]),J)
for w in W:
    for J in subsets:
        for K in subsets:
            if not J <= K: continue
            for L in subsets:
                if K <= L:
                    assert reveal(reveal(record(w,J),K),L)==reveal(record(w,J),L)
            assert transport(reveal(record(w,J),K),K)==reveal(transport(record(w,J),J),K)
    for order in permutations(I):
        state=record(w,set()); J=set()
        for i in order:
            J.add(i); state=reveal(state,J)
        assert state==record(w,I)
# Visible observations cannot replace full latent record before reveal.
assert record(W[0],set())[1] == record(W[-1],set())[1]
assert reveal(record(W[0],set()),I)[1] != reveal(record(W[-1],set()),I)[1]
print('PASS: all subset reveals, permutation/cut laws and native transport squares.')
print('BOUNDARY: tests are finite diagnostics, not proof-assistant certification.')
