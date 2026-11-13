"""Independent enumeration of the bounded random driver; no data fitting."""
from fractions import Fraction as F
from collections import Counter
B=2**20
counts=Counter((200*u)//B for u in range(B))
tv=sum(abs(F(counts[r],B)-F(1,200)) for r in range(200))/2
assert tv==F(33,1638400)
transfer=8*tv
assert transfer==F(33,204800)
combined=F(41397572930541,1024000000000000)+transfer
assert combined==F(41562572930541,1024000000000000)<F(40589,1000000)
print('PASS: source TV',tv,'H8 transfer',transfer,'combined',combined)
