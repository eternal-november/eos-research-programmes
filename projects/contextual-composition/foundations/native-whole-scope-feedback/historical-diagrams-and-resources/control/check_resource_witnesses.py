"""Finite rational diagnostics only; not a proof of native assembly or recurrence."""
from itertools import product
from fractions import Fraction as F
import json
inputs=list(product(range(2),repeat=2))
outputs=inputs
strategies=list(product(range(2),repeat=4))
def out(s,x,y): return (s[x],s[2+y])
def wins(s): return sum((out(s,x,y)[0]^out(s,x,y)[1])==x*y for x,y in inputs)
assert len(strategies)==16
assert max(map(wins,strategies))==3
best=[s for s in strategies if wins(s)==3]
assert len(best)==8
# Uniform optimal strategies give the isotropic local boundary.
K={(x,y,a,b):sum(F(1,8) for s in best if out(s,x,y)==(a,b)) for x,y in inputs for a,b in outputs}
assert all(K[x,y,a,b]==(F(3,8) if a^b==x*y else F(1,8)) for x,y in inputs for a,b in outputs)
# Claimed PR table is a normalized nonsignalling table with win probability one.
PR={(x,y,a,b):F(1,2) if a^b==x*y else F(0) for x,y in inputs for a,b in outputs}
assert all(sum(PR[x,y,a,b] for a,b in outputs)==1 for x,y in inputs)
assert all(sum(PR[x,y,a,b] for b in range(2))==F(1,2) for x,y in inputs for a in range(2))
assert all(sum(PR[x,y,a,b] for a in range(2))==F(1,2) for x,y in inputs for b in range(2))
# Communication repair with shared S and X disclosed to B.
assert all(sum(F(1,2) for s in range(2) if (s,s^(x*y))==(a,b))==PR[x,y,a,b] for x,y in inputs for a,b in outputs)
# Three positive rows force all four outputs zero; the specified zero row cannot follow.
pos=inputs[:3]
positive_good=[s for s in strategies if all(out(s,x,y)==(0,0) for x,y in pos)]
assert len(positive_good)==1
assert all(out(s,1,1)!=(0,1) for s in positive_good)
# Hidden labels with same observation cannot produce label-specific deterministic outputs.
assert not any(all(bit==label for label in range(2)) for bit in range(2))
# Antidiagonal population launch from a fresh shared bit.
anti={y:sum(F(1,2) for s in range(2) if (s,1-s)==y) for y in outputs}
assert anti=={(0,0):F(0),(0,1):F(1,2),(1,0):F(1,2),(1,1):F(0)}
# Retained-memory complete law cannot be replaced by a fresh independent bit.
correlated={(r,a,c):F(1,2) if (a,c)==(r,1-r) else F(0) for r in range(2) for a,c in outputs}
independent={(r,a,c):F(1,4) if a!=c else F(0) for r in range(2) for a,c in outputs}
assert correlated!=independent
assert sum(correlated[r,a,c] for r in range(2) for a,c in outputs if a==r)==1
assert sum(independent[r,a,c] for r in range(2) for a,c in outputs if a==r)==F(1,2)
assert all(sum(correlated[r,a,c] for r in range(2))==sum(independent[r,a,c] for r in range(2)) for a,c in outputs)
# Explicit native raw completion retains even unreachable pairs.
raw=list(product(range(2),outputs))
assert len(raw)==8 and set(y for s,y in raw)==set(outputs)
assert sum(F(1,2) if y==(s,1-s) else F(0) for s,y in raw)==1
print(json.dumps({'status':'PASS','deterministic_strategies':16,'max_CHSH_wins':3,'optimal_strategies':8,'optimal_local_win_probability':'3/4','PR_win_probability':'1','zero_row_positive_only_solutions':1,'all_raw_zero_row_solutions':0,'hidden_label_common_table_solutions':0,'retained_memory_agreement':'1','fresh_replacement_agreement':'1/2','completed_launch_raw_pairs':8,'scope':'exact finite rational witnesses, not formal native or recurrent proof'},indent=2))
