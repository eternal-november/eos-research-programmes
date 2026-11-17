from fractions import Fraction as F
from itertools import product
import json
alpha={0:F(1,2),1:F(1,2)}
constant_beta=dict(alpha)
assert constant_beta==alpha
biased={l:{r:(F(1) if r==l else F(0)) for r in alpha} for l in alpha}
assert all(biased[l]!=alpha for l in alpha)
# actual selection l=R, diag service for0, antidiag for1
W={0:F(0),1:F(0)}
for r in alpha:
    l=r; w=r if l==0 else 1-r; W[w]+=alpha[r]
assert W=={0:F(1),1:F(0)}
S={0:F(0),1:F(1,2),2:F(1,2)}
T={0:F(1,2),1:F(1,2)}; U={0:F(1)}
lamS={0:(F(1),F(0)),1:(F(1),F(0)),2:(F(0),F(1))}
lamT={0:(F(1),F(0)),1:(F(0),F(1))}; lamU={0:(F(1,2),F(1,2))}
f={0:0,1:0,2:1}; g={0:0,1:0}
def joint(prior,lam):return {(r,w):p*lam[r][w] for r,p in prior.items() for w in range(2)}
def push(q,m,targets):return {(t,w):sum(p for (r,x),p in q.items() if m[r]==t and x==w) for t in targets for w in range(2)}
qS,qT,qU=joint(S,lamS),joint(T,lamT),joint(U,lamU)
assert push(qS,f,T)==qT and push(qT,g,U)==qU
assert all(lamS[s]==lamT[f[s]] for s in S)
assert all(S[s]>0 or lamS[s]==lamT[f[s]] for s in S)
assert all(T[t]>0 or lamT[t]==lamU[g[t]] for t in T)
assert lamS[0]!=lamU[g[f[0]]]
assert any((S[s]==0)!=(T[f[s]]==0) for s in S)
assert not all(lamT[t]==lamU[g[t]] for t in T)
print(json.dumps({'constant_diagonal_with_full_available_read_calibrated':True,'reserve_selected_labels_calibrated':False,'biased_naive_W_mass':[str(W[w]) for w in W], 'first_map_strong':True,'second_map_weak_plan_pushforward':True,'both_complete_plan_pushforwards':True,'composite_zero_table_preserved':False,'first_map_support_exact':False,'second_map_strong':False},indent=2))
