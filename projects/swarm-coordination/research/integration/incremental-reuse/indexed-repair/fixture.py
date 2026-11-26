from reuse import Graph, Fact
from dependency import Producer
import plant

def modeled(n):
    g=plant.compile(plant.Mode(False,False))
    gates={k:v for k,v in g.out.items()}
    alt=plant.compile(plant.Mode(True,False))
    slow=plant.compile(plant.Mode(False,True))
    recipes={}
    C=lambda k:('constant',k)
    R=lambda k:('read',k)
    B=lambda p,x,y:('if',p,x,y)
    params={'choose_backup':False,'main_bound':False,'other_bound':False,'late':False}
    # Reuse the raw direct plant. Only the cell adapter knows how the selected
    # world instantiates the old physical law. No public controller sees it.
    for k,v in gates.items():
        recipes[k]=C(v)
        if alt.out[k]!=v:
            recipes[k]=B(B(R('choose_backup'),R('other_bound'),R('main_bound')),
                         C(alt.out[k]),C(v))
        elif slow.out[k]!=v:
            recipes[k]=B(R('late'),C(slow.out[k]),C(v))
    facts=dict(g.facts)
    roots=set(g.roots)
    for j in range(n):
        k=f'untouched-contract-{j}'
        roots.add(k);facts[k]=Fact();recipes[k]=R(k)
        params[k]=frozenset({k})
    prod=Producer(recipes,params)
    return Graph(frozenset(roots),{k:v[0] for k,v in prod.memo.items()},facts),prod

