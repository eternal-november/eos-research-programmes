import itertools,json
out=[]
for n in range(3,11):
 edges=[(i,(i+1)%n,int(i==n-1)) for i in range(n)]
 def count(keep):
  return sum(all(g[a]^g[b]==s for i,(a,b,s) in enumerate(edges) if i in keep) for g in itertools.product(range(2),repeat=n))
 full=count(set(range(n)))
 removals=[count(set(range(n))-{i}) for i in range(n)]
 assert full==0 and all(c==2 for c in removals)
 # Every smaller subfamily is contained in one maximal proper subfamily; its solutions persist.
 out.append(dict(n=n,full_solutions=full,single_chart_removal_solutions=removals))
print(json.dumps(out,indent=2))
