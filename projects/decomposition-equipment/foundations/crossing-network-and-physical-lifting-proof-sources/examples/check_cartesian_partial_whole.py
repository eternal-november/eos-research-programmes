import itertools,json
bits=range(2)
A=[{0,1},{1,2},{2,0}]

def run(twist):
 f=[{0:0,1:0},{1:0,2:0},{0:0,2:twist}]
 # actual full grid checks: theta(alpha(r,t),q,s)=(r,q,beta(t,s))
 events=0
 for i in range(3):
  for a,x,k,v in itertools.product(A[i],bits,bits,bits):
   b=1-x;c=1-b;l=1-k;d=c^l
   p=(a,x,v^f[i][a]);q=k;s=(c,l)
   theta=((a,x),q,(b,l,p[2]^f[i][a]))
   assert theta==((a,x),k,(b,l,v))
   assert d==x^(1-k)
   events+=1
 # Every global alpha at fixed b is three arbitrary permutations, encoded by flips g[a].
 # alpha_global(a,t)=(a,t xor g[a]); h_i(t)=t xor h[i].
 # α_global(a,h_i(t))=α_i(a,t) iff g[a] xor h[i] = f_i[a].
 sols=[]
 for g in itertools.product(bits,repeat=3):
  for h in itertools.product(bits,repeat=3):
   if all(g[a]^h[i]==f[i][a] for i in range(3) for a in A[i]):sols.append((g,h))
 # Normalize global middle name by g[0]=0; remaining solutions are isomorphism classes.
 normalized=[z for z in sols if z[0][0]==0]
 assert len(normalized)==(0 if twist else 1)
 return dict(local_grid_events_checked=events,per_b_global_labelled_solutions=len(sols),per_b_global_isomorphism_classes=len(normalized),full_grid_global_labelled_solutions=len(sols)**2,full_grid_global_isomorphism_classes=len(normalized)**2,solutions=sols)
print(json.dumps({'negative':run(1),'positive':run(0)},indent=2))
