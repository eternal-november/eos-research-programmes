"""Author finite checks for witnessed square classification; Python standard library only."""
import itertools, math, json
from pathlib import Path


def theta_from_fill(l,r,n,alpha,beta):
    # alpha[(ell,u)] -> v; beta[(u,rr)] -> w
    out=[None]*(l*n*r)
    for ell in range(l):
      for u in range(n):
       for rr in range(r):
        v=alpha[ell*n+u];w=beta[u*r+rr]
        out[v*r+rr]=ell*(n*r)+w
    return tuple(out)


def rectangle_test(l,r,v,w,theta):
    if l==0 and r==0:return v==0 and w==0
    if l==0:return v==0 and w%r==0
    if r==0:return w==0 and v%l==0
    # For full visible supports isolate concrete labels, not counts.
    adj=[[] for _ in range(v+w)]
    for x in range(v):
      for rr in range(r):
        ell,y=divmod(theta[x*r+rr],w)
        adj[x].append((v+y,ell,rr));adj[v+y].append((x,ell,rr))
    seen=set()
    for root in range(v+w):
      if root in seen:continue
      stack=[root];seen.add(root);nodes=[]
      while stack:
       x=stack.pop();nodes.append(x)
       for y,_,_ in adj[x]:
        if y not in seen:seen.add(y);stack.append(y)
      left=[x for x in nodes if x<v];right=[x for x in nodes if x>=v]
      if len(left)!=l or len(right)!=r:return False
      ll=[];rrs=[]
      for x in left:
       labs={z[1] for z in adj[x]}
       if len(labs)!=1 or len(adj[x])!=r:return False
       ll.extend(labs)
       if set(z[0] for z in adj[x])!=set(right):return False
      for y in right:
       labs={z[2] for z in adj[y]}
       if len(labs)!=1 or len(adj[y])!=l:return False
       rrs.extend(labs)
      if set(ll)!=set(range(l)) or len(ll)!=len(set(ll)):return False
      if set(rrs)!=set(range(r)) or len(rrs)!=len(set(rrs)):return False
    return True


def main():
  result={'domain':'All singleton-endpoint profiles l,r,v,w in 0..3 with vr=lw<=8, plus l=r=2,v=w=4. All theta bijections. Explicit alpha/beta generation for nonempty supports.','profiles':0,'theta_cases':0,'profiles_detail':[]}
  profiles=[p for p in itertools.product(range(4),repeat=4) if p[2]*p[1]==p[0]*p[3] and p[2]*p[1]<=8]
  profiles.append((2,2,4,4))
  for l,r,v,w in profiles:
    size=v*r
    feasible=[]
    # n<=max(v,w)+1 covers all visible/one-sided solutions and existence of ghosts.
    for n in range(max(v,w)+2):
      if l*n==v and n*r==w:feasible.append(n)
    expected=set()
    if l and r and feasible:
      n=feasible[0]
      for alpha in itertools.permutations(range(v)):
       for beta in itertools.permutations(range(w)):
        expected.add(theta_from_fill(l,r,n,alpha,beta))
    accepted=0;total=0
    for theta in itertools.permutations(range(size)):
      got=rectangle_test(l,r,v,w,theta)
      truth=(theta in expected) if l and r else bool(feasible)
      assert got==truth,(l,r,v,w,theta,got,truth)
      accepted+=got;total+=1
    if l and r and feasible:
      n=feasible[0]
      assert accepted==math.factorial(v)*math.factorial(w)//math.factorial(n)
    result['profiles']+=1;result['theta_cases']+=total
    result['profiles_detail'].append({'l':l,'r':r,'v':v,'w':w,'all_theta':total,'fillable_theta':accepted})
  result['status']='PASS'
  Path(__file__).with_name('check_witnessed_square_results.json').write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps({k:v for k,v in result.items() if k!='profiles_detail'},indent=2))

if __name__=='__main__':main()
