"""Finite author tests of Q/F/L cylinder criterion against explicit alpha0,beta construction."""
import itertools,json
from pathlib import Path
perms=list(itertools.permutations(range(4)))
small=list(itertools.permutations(range(2)))

def descriptor(theta):
    inv=[0]*4
    for p,rn in enumerate(theta):inv[rn]=p
    return ((inv[0],inv[2]),(inv[1],inv[3])) # indexed by actual N witness

def construct(alpha,beta):
    out=[None]*4
    for r in range(2):
      for t in range(2):out[alpha[r*2+t]]=r*2+beta[t]
    return tuple(out)

def main():
  profiles=[];total=0
  for m,q in itertools.product((1,2),repeat=2):
    expected=set()
    for alpha in perms:
      for betas in itertools.product(small,repeat=m):
        expected.add(tuple(construct(alpha,betas[l]) for l in range(m) for j in range(q)))
    assert len(expected)==(24 if m==1 else 48)
    seen=0;accept=0;sets_only=0
    for data in itertools.product(perms,repeat=m*q):
      ds=[descriptor(t) for t in data]
      test_f=all(ds[l*q+j]==ds[l*q] for l in range(m) for j in range(q))
      test_l=all(set(ds[l*q])==set(ds[0]) for l in range(m))
      got=test_f and test_l
      truth=data in expected
      assert got==truth,(m,q,data,ds)
      seen+=1;accept+=got
      sets_only+=all(set(d)==set(ds[0]) for d in ds)
    total+=seen
    profiles.append({'L_values':m,'Q_witnesses_per_value':q,'q_preserving_theta':seen,'coherent_cylinders':accept,'unlabelled_tilings_only':sets_only})
  out={'status':'PASS','domain':'R=2,P=4,S_l=1,N_l=2, singleton other external types; L has1or2 values,Q_l has1or2 actual witnesses. All q-preserving theta, compared to explicit alpha0,beta generated tuples.','total_theta':total,'profiles':profiles}
  Path(__file__).with_name('check_crossing_grid_results.json').write_text(json.dumps(out,indent=2)+'\n')
  print(json.dumps(out,indent=2))
if __name__=='__main__':main()
