#!/usr/bin/env python3
"""C1 author C-evidence. Standard-library exhaustive tests; NOT kernel/P proofs.
The two executable representations are block/edge sets and vertex labels/
adjacency matrices. No baseline file is changed. See DOMAIN.md.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product, combinations, combinations_with_replacement
from pathlib import Path
import argparse, datetime, hashlib, json, sys, time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CONTRACT = '47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET = '7a5d4bb8dd3aa0715c82b73b8c169def2935b98f41addfd0eaaf03a606be244e'

def require(p, msg='check failed'):
    if not p: raise AssertionError(msg)

@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple[tuple[int, int], ...]
    def __post_init__(self):
        require(self.n >= 0)
        require(self.edges == tuple(sorted(set(self.edges))), 'edges not canonical')
        require(all(0 <= a < b < self.n for a,b in self.edges), 'not simple ordered graph')
    def restrict(self, block):
        b = tuple(block)
        require(b == tuple(sorted(set(b))) and all(0 <= x < self.n for x in b))
        rank = {x:i for i,x in enumerate(b)}
        return Graph(len(b), tuple(sorted((rank[a],rank[c]) for a,c in self.edges if a in rank and c in rank)))

@dataclass(frozen=True)
class Arrow:
    source: int
    target: int
    bit: int = 0
    def __post_init__(self):
        require(0 <= self.source <= self.target <= 2, 'invalid chain arrow')
        require(self.bit in (0,1), 'invalid C2 bit')

def compose(arrows, start):
    end, bit = start, 0
    for a in arrows:
        require(a.source == end, 'noncomposable arrows')
        end, bit = a.target, bit ^ a.bit
    return Arrow(start, end, bit)

@dataclass(frozen=True)
class Component:
    graph: Graph
    arrow: Arrow

@dataclass(frozen=True)
class Cut:
    whole: Component
    blocks: tuple[tuple[int, ...], ...]
    arrows: tuple[Arrow, ...]
    def __post_init__(self):
        require(len(self.blocks)==len(self.arrows), 'arity mismatch')
        require(all(b == tuple(sorted(set(b))) for b in self.blocks), 'noncanonical block')
        flat = [v for b in self.blocks for v in b]
        require(sorted(flat)==list(range(self.whole.graph.n)), 'not an ordered partition')
        require(compose(self.arrows,self.whole.arrow.source)==self.whole.arrow, 'wrong whole grade')
    def leaves(self):
        return tuple(Component(self.whole.graph.restrict(b),a) for b,a in zip(self.blocks,self.arrows))

def identity(c):
    return Cut(c,(tuple(range(c.graph.n)),),(c.arrow,))

def substitute(w, forest):
    require(len(forest)==len(w.blocks), 'occurrence arity mismatch')
    blocks, arrows = [], []
    for b,c,v in zip(w.blocks,w.leaves(),forest):
        require(v.whole==c, 'replacement has wrong component')
        blocks.extend(tuple(b[j] for j in d) for d in v.blocks)
        arrows.extend(v.arrows)
    return Cut(w.whole,tuple(blocks),tuple(arrows))

# Independent executable representation: every vertex stores a block label;
# graph restriction scans adjacency MATRIX entries, never Graph.restrict.
@dataclass(frozen=True)
class LabelCut:
    matrix: tuple[tuple[bool, ...], ...]
    whole_grade: tuple[int,int,int]
    labels: tuple[int, ...]
    arity: int
    grades: tuple[tuple[int,int,int], ...]


def matrix(g):
    # Separate adjacency enumeration rather than coordinates in restrict().
    return tuple(tuple((min(i,j),max(i,j)) in g.edges for j in range(g.n)) for i in range(g.n))

def labels(w):
    lab = [None]*w.whole.graph.n
    for i,b in enumerate(w.blocks):
        for v in b: lab[v] = i
    return LabelCut(matrix(w.whole.graph), (w.whole.arrow.source,w.whole.arrow.target,w.whole.arrow.bit), tuple(lab),len(w.blocks),tuple((a.source,a.target,a.bit) for a in w.arrows))

def label_substitute(w, forest):
    require(len(forest)==w.arity)
    offsets = [0]
    for f in forest: offsets.append(offsets[-1]+f.arity)
    # Each vertex's rank is counted from earlier vertices with its label.
    result = []
    for vertex,outer in enumerate(w.labels):
        local = sum(1 for v in range(vertex) if w.labels[v]==outer)
        result.append(offsets[outer]+forest[outer].labels[local])
    return LabelCut(w.matrix,w.whole_grade,tuple(result),offsets[-1],tuple(g for f in forest for g in f.grades))

def label_leaf_matrices(w):
    ans=[]
    for i in range(w.arity):
        chosen=[j for j,x in enumerate(w.labels) if x==i]
        ans.append(tuple(tuple(w.matrix[a][b] for b in chosen) for a in chosen))
    return tuple(ans)

def partitions(m,n):
    for assignment in product(range(n), repeat=m):
        yield tuple(tuple(v for v,a in enumerate(assignment) if a==i) for i in range(n))

def graphs(m):
    pairs=list(combinations(range(m),2))
    for mask in range(1<<len(pairs)):
        yield Graph(m,tuple(p for i,p in enumerate(pairs) if mask>>i&1))

def paths(n,a=0,b=2, fixed_ends=False):
    if fixed_ends:
        if n==0:
            if a==b: yield ()
            return
        for middle in combinations_with_replacement(range(a,b+1),n-1):
            verts=(a,)+middle+(b,)
            yield tuple(Arrow(x,y) for x,y in zip(verts,verts[1:]))
    else:
        for verts in combinations_with_replacement(range(3),n+1):
            yield verts[0],tuple(Arrow(x,y) for x,y in zip(verts,verts[1:]))

def cut_for(g,bs,arr,start):
    return Cut(Component(g,compose(arr,start)),bs,tuple(arr))

def expect_rejected(fn):
    try: fn()
    except AssertionError: return True
    return False

def six_vertex():
    g=Graph(6,((0,1),(1,2),(1,3),(2,4),(3,4),(4,5)))
    bs=((0,),(1,3),(2,4),(5,))
    arr=(Arrow(0,1),Arrow(1,1),Arrow(1,1),Arrow(1,2))
    w=cut_for(g,bs,arr,0)
    cs=w.leaves()
    require(cs[1]==cs[2] and cs[1].graph.n==2 and cs[1].graph.edges==((0,1),))
    forward=Cut(cs[1],((0,),(1,)),(Arrow(1,1),)*2)
    reverse=Cut(cs[2],((1,),(0,)),(Arrow(1,1),)*2)
    require(forward!=reverse and forward.leaves()==reverse.leaves())
    forest=(identity(cs[0]),forward,reverse,identity(cs[3]))
    refined=substitute(w,forest)
    require(refined.blocks==((0,),(1,),(3,),(4,),(2,),(5,)))
    require(labels(refined)==label_substitute(labels(w),tuple(map(labels,forest))))

    # Build full binary trees recursively; node labels store REAL whole cuts.
    # Leaves carry only component; node's cut stores retained graph + inclusions.
    def make_tree(shape, ambient, vertex_path):
        if isinstance(shape,int): return ('leaf',Component(ambient,Arrow(vertex_path[0],vertex_path[-1])))
        left,right=shape
        def leaves(s): return [s] if isinstance(s,int) else leaves(s[0])+leaves(s[1])
        ids=leaves(shape); left_ids=leaves(left); right_ids=leaves(right)
        root_vertices=sorted(v for i in ids for v in bs[i])
        rank={v:j for j,v in enumerate(root_vertices)}
        lblock=tuple(sorted(rank[v] for i in left_ids for v in bs[i]))
        rblock=tuple(sorted(rank[v] for i in right_ids for v in bs[i]))
        split=len(left_ids)
        a,b,c=vertex_path[0],vertex_path[split],vertex_path[-1]
        node=cut_for(ambient,(lblock,rblock),(Arrow(a,b),Arrow(b,c)),a)
        return ('node',node,make_tree(left,ambient.restrict(lblock),vertex_path[:split+1]),make_tree(right,ambient.restrict(rblock),vertex_path[split:]))
    def evaluate(tree):
        return identity(tree[1]) if tree[0]=='leaf' else substitute(tree[1],(evaluate(tree[2]),evaluate(tree[3])))
    left=make_tree(((0,1),(2,3)),g,(0,1,1,1,2))
    right=make_tree((0,(1,(2,3))),g,(0,1,1,1,2))
    require(left!=right and evaluate(left)==evaluate(right)==w)
    gp=Graph(6,tuple(sorted(g.edges+((0,5),))))
    wp=cut_for(gp,bs,arr,0)
    require(w.leaves()==wp.leaves() and w.whole!=wp.whole and w!=wp)

    empty=Component(Graph(0,()),Arrow(1,1))
    nullary=Cut(empty,(),())
    require(identity(empty)!=nullary and len(identity(empty).blocks)==1 and len(nullary.blocks)==0)
    require(substitute(identity(empty),(nullary,))==nullary)
    # C2-category grade retains an actual nonidentity loop despite same endpoints.
    bad_loop=Component(Graph(0,()),Arrow(1,1,1))
    bad_ends=Component(Graph(0,()),Arrow(0,1))
    rejection={
      'nonidentity_loop_nullary':expect_rejected(lambda:Cut(bad_loop,(),())),
      'unequal_endpoint_nullary':expect_rejected(lambda:Cut(bad_ends,(),())),
      'nonempty_graph_nullary':expect_rejected(lambda:Cut(cs[1],(),())),
      'overlapping_partition':expect_rejected(lambda:Cut(w.whole,((0,1,2),(2,3,4,5)),(Arrow(0,1),Arrow(1,2)))),
      'missing_vertex_partition':expect_rejected(lambda:Cut(w.whole,((0,1,2),(3,4)),(Arrow(0,1),Arrow(1,2)))),
      'noncomposable_arrow_string':expect_rejected(lambda:Cut(w.whole,bs,(Arrow(0,1),Arrow(0,1),Arrow(1,1),Arrow(1,2)))),
      'wrong_grade_same_endpoints':expect_rejected(lambda:Cut(w.whole,bs,(Arrow(0,1,1),)+arr[1:])),
    }
    require(all(rejection.values()))
    # Negative controls deliberately alter exactly the claimed retained datum.
    # A mutation is KILLED iff its output differs from the known-correct property.
    collapse={c:v for c,v in zip(cs,forest)}
    collapsed=substitute(w,tuple(collapse[c] for c in cs))
    no_lift=tuple(d for f in forest for d in f.blocks)
    # Concrete bad acceptance predicates: they deliberately omit a required
    # condition and must admit the corresponding known-invalid datum.
    def mutant_nullary_allowed(c):
        return c.graph.n==0 and c.arrow.source==c.arrow.target  # DROPS bit
    bad_string=(Arrow(0,1),Arrow(0,1),Arrow(1,1),Arrow(1,2))
    def mutant_accept_arrow_string(whole, arrows):
        return bool(arrows) and arrows[0].source==whole.arrow.source and arrows[-1].target==whole.arrow.target
    def mutant_erase_empty_blocks(cut):
        return tuple(b for b in cut.blocks if b)
    mutations={
      'erase_whole': {'killed':(w.blocks,w.arrows)==(wp.blocks,wp.arrows) and w!=wp,
                     'reason':'coarser output collapses the certified distinct whole pair'},
      'collapse_occurrences_by_colour': {'killed':collapsed!=refined,'mutant_blocks':collapsed.blocks},
      'ignore_canonical_lift': {'killed':no_lift!=refined.blocks,'mutant_blocks':no_lift},
      'forget_arrow_values': {'killed':mutant_nullary_allowed(bad_loop) and rejection['nonidentity_loop_nullary'], 'mutant_accepts_invalid_nonidentity_loop_nullary':mutant_nullary_allowed(bad_loop)},
      'forget_arrow_composability': {'killed':mutant_accept_arrow_string(w.whole,bad_string) and rejection['noncomposable_arrow_string'], 'mutant_accepts_noncomposable_string':mutant_accept_arrow_string(w.whole,bad_string)},
      'empty_identity_leaf_is_nullary': {'killed':mutant_erase_empty_blocks(identity(empty))==nullary.blocks and identity(empty)!=nullary, 'mutant_blocks':mutant_erase_empty_blocks(identity(empty))},
    }
    require(all(v['killed'] for v in mutations.values()))
    return {'base_graph':{'vertices':6,'edges':g.edges},'base_blocks':bs,'interface_vertices':(0,1,1,1,2),
      'middle_component':{'vertices':2,'edges':cs[1].graph.edges,'arrow':(1,1,0)},
      'local_middle_refinements':(forward.blocks,reverse.blocks),'refined_blocks':refined.blocks,
      'competing_tree_shapes':('((0,1),(2,3))','(0,(1,(2,3)))'),
      'competing_trees_distinct':True,'same_full_flat_cut':True,'cross_edge_added':(0,5),
      'same_induced_leaves_distinct_wholes':True,'rejections':rejection,'mutations':mutations}

def basic_suite():
    count={'graphs':0,'cuts':0,'single_occurrence_refinements':0,'canonical_nested_restrictions':0,
           'left_unit':0,'right_unit':0,'redundant_label_substitutions':0}
    for m in range(4):
      for g in graphs(m):
        count['graphs']+=1
        # Every B subset [m] and C subset [|B|], independent of partitions.
        for mask in range(1<<m):
          b=tuple(v for v in range(m) if mask>>v&1)
          for inner in range(1<<len(b)):
            c=tuple(i for i in range(len(b)) if inner>>i&1)
            image=tuple(b[i] for i in c)
            require(g.restrict(b).restrict(c)==g.restrict(image))
            # Sorted enumeration composition, including empty supports.
            require(tuple(sorted(image))==tuple(b[i] for i in sorted(c)))
            count['canonical_nested_restrictions']+=1
        for n in range(4):
          for bs in partitions(m,n):
            for start,arr in paths(n):
              w=cut_for(g,bs,arr,start); count['cuts']+=1
              lw=labels(w)
              require(label_leaf_matrices(lw)==tuple(matrix(c.graph) for c in w.leaves()))
              ids=tuple(identity(c) for c in w.leaves())
              require(substitute(w,ids)==w); count['right_unit']+=1
              require(substitute(identity(w.whole),(w,))==w); count['left_unit']+=1
              for i,c in enumerate(w.leaves()):
                for k in range(3):
                  for ds in partitions(c.graph.n,k):
                    for gs in paths(k,c.arrow.source,c.arrow.target,True):
                      v=Cut(c,ds,gs)
                      forest=ids[:i]+(v,)+ids[i+1:]
                      z=substitute(w,forest)
                      require(z.whole==w.whole)
                      require(labels(z)==label_substitute(lw,tuple(map(labels,forest))))
                      require(z.leaves()==tuple(cc for vv in forest for cc in vv.leaves()))
                      count['single_occurrence_refinements']+=1
                      count['redundant_label_substitutions']+=1
    return count

# Depth-three shapes: n outer children, k_i grandchildren, ell_ij leaves.
# Every local arity belongs to {0,1,2}; shapes retain zero-ary nodes.
def shapes():
    for n in range(3):
      for ks in product(range(3),repeat=n):
        for ls in product(range(3),repeat=sum(ks)):
          ans=[];off=0
          for k in ks: ans.append(tuple(ls[off:off+k]));off+=k
          yield tuple(ans)

def associativity_suite():
    counts={'shapes':0,'graph_shape_label_assignments':0,'interface_shape_chains':0,
            'factorized_full_cases':0,'full_cut_associativity_comparisons':0}
    shape_domain=list(shapes());counts['shapes']=len(shape_domain)
    interfaces_by_leaves={l:list(combinations_with_replacement(range(3),l+1)) for l in range(9)}
    # Arrow side checked for EVERY final chain and EVERY shape. Internal arrow
    # endpoints are forced by each node's contiguous interval of final leaves.
    for shape in shape_domain:
      L=sum(sum(row) for row in shape)
      for chain in interfaces_by_leaves[L]:
        offsets=[0];mid_arrows=[];inner_arrows=[];outer_arrows=[]
        cur=0
        for row in shape:
          row_start=cur; mids=[]
          for ell in row:
            finals=tuple(Arrow(chain[t],chain[t+1]) for t in range(cur,cur+ell))
            mid=Arrow(chain[cur],chain[cur+ell])
            require(compose(finals,chain[cur])==mid)
            mids.append(mid);inner_arrows.extend(finals);cur+=ell
          out=Arrow(chain[row_start],chain[cur]);require(compose(mids,chain[row_start])==out)
          outer_arrows.append(out);mid_arrows.extend(mids)
        require(compose(outer_arrows,chain[0])==compose(mid_arrows,chain[0])==compose(inner_arrows,chain[0]))
        counts['interface_shape_chains']+=1
      for m in range(4):
        for g in graphs(m):
          for assignment in product(range(L),repeat=m):
            final_blocks=tuple(tuple(v for v,a in enumerate(assignment) if a==i) for i in range(L))
            # Graph/canonical-coordinate side at constant interface 1: because
            # graph operations never inspect arrows, this factors ALL chains.
            flat_i=0;outer_blocks=[];middle_ambient=[];bottom_ambient=[]
            for row in shape:
              mids=[];bottoms=[]
              for ell in row:
                finals=final_blocks[flat_i:flat_i+ell];flat_i+=ell
                mids.append(tuple(sorted(v for block in finals for v in block)));bottoms.append(finals)
              outer_blocks.append(tuple(sorted(v for block in mids for v in block)))
              middle_ambient.append(mids);bottom_ambient.append(bottoms)
            outer=cut_for(g,tuple(outer_blocks),(Arrow(1,1),)*len(shape),1)
            middle=[];bottom=[]
            for i,row in enumerate(shape):
              e=outer_blocks[i];rank={v:t for t,v in enumerate(e)}
              mids=tuple(tuple(rank[v] for v in block) for block in middle_ambient[i])
              mid=Cut(outer.leaves()[i],mids,(Arrow(1,1),)*len(row));middle.append(mid)
              bs=[]
              for j,ell in enumerate(row):
                ambient=middle_ambient[i][j];rank2={v:t for t,v in enumerate(ambient)}
                ds=tuple(tuple(rank2[v] for v in d) for d in bottom_ambient[i][j])
                bs.append(Cut(mid.leaves()[j],ds,(Arrow(1,1),)*ell))
              bottom.append(tuple(bs))
            left=substitute(substitute(outer,tuple(middle)),tuple(v for row in bottom for v in row))
            right=substitute(outer,tuple(substitute(v,row) for v,row in zip(middle,bottom)))
            expected=cut_for(g,final_blocks,(Arrow(1,1),)*L,1)
            require(left==right==expected)
            lo=labels(outer);lm=tuple(map(labels,middle));lb=tuple(tuple(map(labels,row)) for row in bottom)
            ll=label_substitute(label_substitute(lo,lm),tuple(v for row in lb for v in row))
            lr=label_substitute(lo,tuple(label_substitute(v,row) for v,row in zip(lm,lb)))
            require(ll==lr==labels(expected))
            counts['graph_shape_label_assignments']+=1
            counts['full_cut_associativity_comparisons']+=1
            counts['factorized_full_cases']+=len(interfaces_by_leaves[L])
    return counts

def hash_file(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=HERE/'results.json');args=parser.parse_args()
    start=time.time()
    require(hash_file(ROOT/'research/CompletionContract.md')==CONTRACT,'contract hash changed')
    require(hash_file(ROOT/'research/workstream_C1/C1_Targets.md')==TARGET,'target hash changed')
    result={'status':'RUNNING','evidence':'C: Python computation, not kernel proof or unrestricted theorem',
      'contract_sha256':CONTRACT,'target_sha256':TARGET,'source_sha256':hash_file(Path(__file__)),
      'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'python_version':sys.version,'finite_domain':'DOMAIN.md','full_C1_status':'OPEN; downstream C5/F2 not attempted'}
    try:
      result['six_vertex']=six_vertex(); print('Six-vertex and boundary/mutation certificates PASS',flush=True)
      result['basic_suite']=basic_suite(); print('Basic exhaustive suite',result['basic_suite'],flush=True)
      result['associativity_suite']=associativity_suite();print('Associativity factorized exhaustive suite',result['associativity_suite'],flush=True)
      result['status']='PASS'
    except Exception as exc:
      result['status']='FAIL';result['error']=repr(exc);raise
    finally:
      result['duration_seconds']=time.time()-start
      result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
      args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('Result:',args.output)
if __name__=='__main__': main()
