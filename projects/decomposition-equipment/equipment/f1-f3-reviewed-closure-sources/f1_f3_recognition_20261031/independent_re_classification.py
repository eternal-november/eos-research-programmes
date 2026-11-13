if not __debug__:
    raise RuntimeError("Assertions are required; do not run with -O")
import itertools,json
P=list(itertools.permutations(range(3))); identity=(0,1,2)
def compose(p,q):return tuple(p[q[i]] for i in range(3))
groups=[]
for mask in range(1<<6):
 H={P[i] for i in range(6) if mask>>i&1}
 if identity in H and all(compose(p,q) in H for p in H for q in H):groups.append(H)
pairs=list(itertools.combinations(range(3),2))
def typ(E,U):return tuple((i,j) for i,j in itertools.combinations(range(len(U)),2) if tuple(sorted((U[i],U[j]))) in E)
def closure(gens):
 H={identity}; change=True
 while change:
  new=H|{compose(p,q) for p in H for q in gens};change=new!=H;H=new
 return H
checks=0;valid=0;records=[]
for code in range(8):
 E={pairs[i] for i in range(3) if code>>i&1}
 for edge,nonedge in itertools.product([False,True],repeat=2):
  def local(U):
   if len(U)<2:return {tuple(range(len(U)))}
   if len(U)==3:return H
   active=edge if typ(E,U) else nonedge
   return {(0,1),(1,0)} if active else {(0,1)}
  expectedgens=[]
  for i,j in pairs:
   if (edge if (i,j) in E else nonedge):
    t=list(identity);t[i],t[j]=t[j],t[i];expectedgens.append(tuple(t))
  expected=closure(expectedgens)
  def cluster(E):
   # All triples must be clique components; on three vertices any two-edge pattern fails.
   if len(E)==2:return False
   if E=={(0,2)}:return False
   return True
  allowed=True
  if edge and not nonedge:allowed=cluster(E)
  elif nonedge and not edge:allowed=cluster(set(pairs)-E)
  elif edge and nonedge:allowed=len(E) in (0,3)
  for H in groups:
   R=Eok=True
   for k in range(4):
    for Ut in itertools.combinations(range(3),k):
     U=list(Ut)
     for g in H:
      gU=sorted(g[u] for u in U);rho=tuple(gU.index(g[u]) for u in U)
      R &= typ(E,U)==typ(E,gU) and rho in local(U)
     for h in local(U):
      e=list(identity)
      for i,u in enumerate(U):e[u]=U[h[i]]
      Eok &= tuple(e) in H
   actual=R and Eok;want=allowed and H==expected
   assert actual==want,(code,edge,nonedge,H,R,Eok,want)
   checks+=1;valid+=actual
  records.append({'graph_code':code,'edge_bit':edge,'nonedge_bit':nonedge,'allowed':allowed,'expected_group_order':len(expected) if allowed else None})
result={'status':'PASS','groups_S3':len(groups),'candidate_checks':checks,'valid_candidates':valid,'records':records}
print(json.dumps({k:v for k,v in result.items() if k!='records'}))
from pathlib import Path
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
