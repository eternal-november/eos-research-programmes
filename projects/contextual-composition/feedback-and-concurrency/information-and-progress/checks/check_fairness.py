# Finite lasso diagnostics, not proof verification.
def weak_fair(enabled,fired):
    return (not all(enabled)) or any(fired)
def strong_fair(enabled,fired):
    return (not any(enabled)) or any(fired)
# u->v advances to a tick; v->u stutters. Neither fires task j.
s_en=[True,False];s_fire=[False,False];adv=[1,0]
t_en=[True];t_fire=[False]
assert weak_fair(s_en,s_fire) and not weak_fair(t_en,t_fire)
assert all(s_en[i] for i,a in enumerate(adv) if a)
assert not all(s_en)
assert not strong_fair(s_en,s_fire)
# Silent transition v(rank1)->u(rank0) strictly descends.
rank=[0,1]
assert all(rank[(i+1)%2]<rank[i] for i,a in enumerate(adv) if not a)
# Productive unit-step clocks compose as claimed on finite samples.
from itertools import product
for a in product((0,1),repeat=5):
    l=[0]
    for x in a:l.append(l[-1]+x)
    for b in product((0,1),repeat=5):
        r=[0]
        for x in b:r.append(r[-1]+x)
        comp=[r[x] for x in l]
        assert all(comp[i+1]-comp[i] in (0,1) for i in range(5))
print('PASS: weak-fairness silent-disable boundary, silent rank, 1024 finite clock compositions')
# Universal synchronized partner readiness is exactly event/task-menu inclusion.
U={0,1}
sub=[set(i for i in U if mask>>i&1) for mask in range(4)]
count=0
for S in sub:
 for Sj in sub:
  if not Sj<=S:continue
  for T in sub:
   for Tj in sub:
    if not Tj<=T:continue
    criterion=T<=S and Tj<=Sj
    universal=True
    for C in sub:
     for Cp in sub:
      if not Cp<=C:continue
      if (bool(Tj&C) and not bool(Sj&C)) or (bool(T&Cp) and not bool(S&Cp)):
       universal=False
    assert criterion==universal
    count+=1
print('PASS: universal partner event-menu criterion on',count,'menu pairs')
