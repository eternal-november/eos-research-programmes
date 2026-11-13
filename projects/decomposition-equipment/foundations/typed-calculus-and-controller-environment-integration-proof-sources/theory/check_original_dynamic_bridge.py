"""Finite regressions for the mathematical original-core bridge; not Lean verification."""
from itertools import product
import json
from pathlib import Path

def tuples(carriers, labels):
    return [x for x in product(*carriers) if all(labels[i][x[i]] == labels[i+1][x[i+1]] for i in range(len(x)-1))]

def bijective(f, domain, codomain):
    return len({f[x] for x in domain}) == len(domain) and {f[x] for x in domain} == set(codomain)

results={}
# Three identical colors, separate occurrence coordinates; states and parallel
# events are separate sorts. A boundary label does NOT identify actual records.
checks=0
for n in range(1,5):
    carrier=list(range(n))
    for labels_tuple in product(range(2), repeat=n):
        lab=dict(zip(carrier, labels_tuple))
        pair=tuples([carrier]*2,[lab]*2)
        triple=tuples([carrier]*3,[lab]*3)
        # Independent two grouping witnesses produce same flat map.
        left={x:((x[0],x[1]),x[2]) for x in triple}
        right={x:(x[0],(x[1],x[2])) for x in triple}
        lflat={x:left[x][0]+(left[x][1],) for x in triple}
        rflat={x:(right[x][0],)+right[x][1] for x in triple}
        assert lflat==rflat=={x:x for x in triple}
        assert bijective(left,triple,list(left.values()))
        assert bijective(right,triple,list(right.values()))
        # Flat occurrence expansion identity + 3-level association.
        for x in triple:
            u=tuple((v,v) for v in x)
            v=tuple(tuple((a,a) for a in row) for row in u)
            route1=tuple(a for row in v for cell in row for a in cell)
            route2=tuple(a for row in v for a in tuple(z for cell in row for z in cell))
            assert route1==route2
            checks+=1
results['grouping_and_occurrence_instances']=checks
# Two actual indistinguishable response records, exchanged by a graph automorphism.
# Both loop at same state and emit the same visible response, but maps differ.
events=['touch_record_0','touch_record_1']
identity={e:e for e in events}; swap={events[0]:events[1],events[1]:events[0]}
visible={e:'contact' for e in events}
assert identity!=swap
assert {e:visible[identity[e]] for e in events}=={e:visible[swap[e]] for e in events}
results['parallel_record_equation_rejected']=True
# Nonexact maps remain valid; exact composite does not reflect nodes.
assert not bijective({0:0},[0],[0,1])
assert not bijective({0:0,1:0},[0,1],[0])
assert bijective({0:0},[0],[0])
# Distinct occurrence replacement maps can produce same whole composite.
a={0:0}; u={0:0,1:1}; v={0:0,1:0}
assert u!=v and {x:u[a[x]] for x in a}=={x:v[a[x]] for x in a}
results['nonexact_and_nonfaithfulness_controls']=3
# Boundary coarsening exactness, including all sizes up to three and empties.
coarsen=0
for nd in range(4):
 for nf in range(4):
  for dl in product(range(2),repeat=nd):
   for fl in product(range(2),repeat=nf):
    fine={(d,f) for d in range(nd) for f in range(nf) if dl[d]==fl[f]}
    coarse=set(product(range(nd),range(nf)))
    no_new=all(dl[d]==fl[f] for d,f in coarse)
    assert (fine==coarse)==no_new
    coarsen+=1
results['coarsening_cases']=coarsen
# Nullary endpoint restriction diagonal: is iso exactly when h injective.
nullary=0
for n in range(5):
 for h in product(range(2),repeat=n):
    kernel={(x,y) for x in range(n) for y in range(n) if h[x]==h[y]}
    diagonal={(x,x) for x in range(n)}
    assert (diagonal==kernel)==(len(set(h))==n)
    nullary+=1
results['nullary_diagonal_cases']=nullary
# Sortwise surjective graph map does NOT ensure graph section.
# Directed two-cycle -> one loop. Neither lifted vertex has a loop.
s={0:0,1:1}; t={0:1,1:0}
sections=[(vertex,edge) for vertex in range(2) for edge in range(2)
          if s[edge]==vertex and t[edge]==vertex]
assert sections==[]
results['surjective_cover_without_graph_section']=True
# All-length temporal/spatial comparison on nontrivial directed graphs over J.
# Each component has states (boundary,bit) and edges (boundary,bit,nextbit,record).
Jstates=range(2)
X=list(product(Jstates,range(2)))
E=list(product(Jstates,range(2),range(2),range(2)))
src=lambda e:(e[0],e[1]); tgt=lambda e:(1-e[0],e[2])
def paths(n):
 if n==0:return [((x,),()) for x in X]
 out=[]
 for es in product(E,repeat=n):
  if all(tgt(es[i])==src(es[i+1]) for i in range(n-1)):
   out.append(((src(es[0]),)+tuple(tgt(e) for e in es),es))
 return out
pathchecks=0
for n in range(3):
 ps=paths(n)
 for p,q in product(ps,repeat=2):
  if tuple(x[0] for x in p[0])!=tuple(x[0] for x in q[0]):continue
  if tuple(e[0] for e in p[1])!=tuple(e[0] for e in q[1]):continue
  wp=(tuple(zip(p[0],q[0])),tuple(zip(p[1],q[1])))
  assert all((tgt(wp[1][i][0]),tgt(wp[1][i][1]))==wp[0][i+1] for i in range(n))
  back=( (tuple(x[0] for x in wp[0]),tuple(e[0] for e in wp[1])),
         (tuple(x[1] for x in wp[0]),tuple(e[1] for e in wp[1])) )
  assert back==(p,q)
  pathchecks+=1
results['nontrivial_path_comparison_cases']=pathchecks
# Common-interface base change retains ONE shared lifted label. Exhaustively
# test finite fibres; surjective h reflects bijectivity of a specified map.
basechecks=0
for nsrc in range(4):
 for ntgt in range(4):
  if ntgt==0 and nsrc: continue
  for f in product(range(ntgt),repeat=nsrc):
   for targetlab in product(range(2),repeat=ntgt):
    sourcelab=tuple(targetlab[f[x]] for x in range(nsrc))
    for nh in range(4):
     for h in product(range(2),repeat=nh):
      src=[(x,y) for x in range(nsrc) for y in range(nh) if sourcelab[x]==h[y]]
      tgt=[(x,y) for x in range(ntgt) for y in range(nh) if targetlab[x]==h[y]]
      fb={(x,y):(f[x],y) for x,y in src}
      old=bijective(dict(enumerate(f)),list(range(nsrc)),list(range(ntgt)))
      new=bijective(fb,src,tgt)
      assert not old or new
      if set(h)=={0,1}: assert old==new
      basechecks+=1
results['common_base_change_cases']=basechecks
# Erasing both exact spatial identity components returns boundary, not unit.
B=[0,1]
for b in B:
 outer=(b,b)
 first_empty=outer[0]; second_empty=outer[1]
 assert first_empty==second_empty==b
results['all_nullary_branch_boundary_values']=len(B)
out=Path(__file__).with_name('check_original_dynamic_bridge_results.json')
out.write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
