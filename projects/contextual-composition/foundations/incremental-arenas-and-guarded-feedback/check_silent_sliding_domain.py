from itertools import product
import json
def wf(E,X):
    active=set();done=set()
    def visit(x):
        if x in active:return False
        if x in done:return True
        active.add(x)
        for a,b in E:
            if a==x and not visit(b):return False
        active.remove(x);done.add(x);return True
    return all(visit(x) for x in X)
cases=0
for nv in range(4):
 for nu in range(1,4):
  V=range(nv);U=range(nu)
  for gvalues in product(U,repeat=nv):
   g=dict(zip(V,gvalues));pairs=list(product(U,V))
   for flags in product((0,1),repeat=len(pairs)):
    emits={pair for pair,b in zip(pairs,flags) if b}
    S={(v,w) for v in V for w in V if (g[v],w) in emits}
    T={(u,g[w]) for u,w in emits}
    assert wf(S,V)==wf(T,U)
    cases+=1
print(json.dumps({'status':'passed','relation_function_cases':cases,'includes':'empty V, nonsurjective and noninjective g, silent self loops'},indent=2))
