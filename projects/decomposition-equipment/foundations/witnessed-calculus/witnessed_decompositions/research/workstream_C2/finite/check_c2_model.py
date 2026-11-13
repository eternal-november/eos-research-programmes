#!/usr/bin/env python3
"""C2 deterministic finite certificate. Evidence C, never unrestricted proof.

All finite interfaces use zero-based element coordinates, with separate labels.
No third-party modules. --output stores a deterministic certificate; timings go
only to stdout. The independently authored checker must not import this file.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path
import time

CONTRACT_SHA256 = '47c53465b745aaa0397d8972cdc760de7da1f9c86bcab0e3bbeecf0aaf6a165e'
TARGET_SHA256 = 'b6711190a46b19205ef25f439105eaf1951137d90f5e55a595ea67daf172e2f4'
SIZES = (0, 1, 2)

@lru_cache(None)
def masks(a, b):
    return tuple(range(1 << (a*b)))

@lru_cache(None)
def functions(a, b):
    """All functions [a] -> [b], including the unique empty function."""
    return tuple(product(range(b), repeat=a))

@lru_cache(None)
def supersets(mask, a, b):
    return tuple(w for w in masks(a, b) if mask & ~w == 0)

@lru_cache(None)
def diagonal(a):
    return sum(1 << (i*a+i) for i in range(a))

@lru_cache(None)
def join(a, b, c, r, s):
    """Boolean-matrix composition, bit rows scanned independently of paths."""
    out = 0
    rowmask = (1 << c)-1
    for x in range(a):
        outrow = 0
        for y in range(b):
            if r & (1 << (x*b+y)):
                outrow |= (s >> (y*c)) & rowmask
        out |= outrow << (x*c)
    return out

@lru_cache(None)
def pull(a, b, r, f, g):
    """f:[a']→[a], g:[b']→[b]."""
    return sum(1 << (x*len(g)+y)
               for x in range(len(f)) for y in range(len(g))
               if r & (1 << (f[x]*b+g[y])))

@lru_cache(None)
def chain(sizes, relations):
    if len(sizes) != len(relations)+1:
        raise ValueError('path dimensions do not match arity')
    out = diagonal(sizes[0])
    for i, relation in enumerate(relations):
        out = join(sizes[0], sizes[i], sizes[i+1], out, relation)
    return out

@lru_cache(None)
def realizers(sizes, relations):
    """Independent global truth-table evaluator: enumerate all vertex tuples."""
    if len(sizes) != len(relations)+1:
        raise ValueError('bad truth-table shape')
    return tuple(xs for xs in product(*(range(a) for a in sizes))
                 if all(r & (1 << (xs[i]*sizes[i+1]+xs[i+1]))
                        for i, r in enumerate(relations)))

@lru_cache(None)
def global_chain(sizes, relations):
    return sum(1 << (x*sizes[-1]+y)
               for x, y in set((xs[0], xs[-1])
                               for xs in realizers(sizes, relations)))

@dataclass(frozen=True)
class Interface:
    label: str
    size: int
    def __post_init__(self):
        if self.size < 0:
            raise ValueError('negative interface size')

@dataclass(frozen=True)
class Relation:
    source: Interface
    target: Interface
    mask: int
    def __post_init__(self):
        if not 0 <= self.mask < (1 << (self.source.size*self.target.size)):
            raise ValueError('relation has out-of-domain entries')

@dataclass(frozen=True)
class Profile:
    source: Interface
    target: Interface
    edges: tuple[Relation, ...]
    def __post_init__(self):
        current = self.source
        for edge in self.edges:
            if current != edge.source:
                raise ValueError('noncomposable ordered profile')
            current = edge.target
        if current != self.target:
            raise ValueError('wrong profile target; nullaries must be loops')
    @property
    def interfaces(self):
        return (self.source,) + tuple(e.target for e in self.edges)
    @property
    def composite(self):
        return Relation(self.source, self.target,
                        chain(tuple(i.size for i in self.interfaces),
                              tuple(e.mask for e in self.edges)))

@dataclass(frozen=True)
class Cell:
    whole: Relation
    profile: Profile
    def __post_init__(self):
        if (self.whole.source, self.whole.target) != (self.profile.source, self.profile.target):
            raise ValueError('whole and full profile endpoints disagree')
        if self.profile.composite.mask & ~self.whole.mask:
            raise ValueError('composite is not contained in whole')
    @property
    def exact(self):
        return self.profile.composite == self.whole


def exact_cell(whole, profile):
    result = Cell(whole, profile)
    if not result.exact:
        raise ValueError('containment cell is not exact')
    return result


def singleton(r):
    return Cell(r, Profile(r.source, r.target, (r,)))


def substitute(outer, children):
    children = tuple(children)
    if tuple(c.whole for c in children) != outer.profile.edges:
        raise ValueError('replacement family has wrong occurrence outputs')
    p = Profile(outer.whole.source, outer.whole.target,
                tuple(r for child in children for r in child.profile.edges))
    return Cell(outer.whole, p)

@dataclass(frozen=True)
class InterfaceMap:
    source: Interface
    target: Interface
    values: tuple[int, ...]
    def __post_init__(self):
        if len(self.values) != self.source.size or any(x < 0 or x >= self.target.size for x in self.values):
            raise ValueError('invalid finite interface map')
    def after(self, previous):
        if previous.target != self.source:
            raise ValueError('interface maps do not compose')
        return InterfaceMap(previous.source, self.target,
                            tuple(self.values[x] for x in previous.values))


def restrict_relation(r, f, g):
    if f.target != r.source or g.target != r.target:
        raise ValueError('restriction maps have incorrect original endpoints')
    return Relation(f.source, g.source,
                    pull(r.source.size, r.target.size, r.mask, f.values, g.values))


def restrict_cell(cell, maps):
    maps = tuple(maps)
    if tuple(f.target for f in maps) != cell.profile.interfaces:
        raise ValueError('one compatible map at each profile boundary required')
    rs = tuple(restrict_relation(r, maps[i], maps[i+1])
               for i, r in enumerate(cell.profile.edges))
    p = Profile(maps[0].source, maps[-1].source, rs)
    return Cell(restrict_relation(cell.whole, maps[0], maps[-1]), p)


def restrict_family(cell, family):
    # A global per-interface map gives exactly the required gluing incidence.
    return restrict_cell(cell, tuple(family[i] for i in cell.profile.interfaces))

@dataclass(frozen=True)
class Generator:
    name: str
    image: Cell

@dataclass(frozen=True)
class Leaf:
    whole: Relation
    @property
    def profile(self):
        return Profile(self.whole.source, self.whole.target, (self.whole,))

@dataclass(frozen=True)
class Node:
    generator: Generator
    children: tuple
    def __post_init__(self):
        if tuple(t.whole for t in self.children) != self.generator.image.profile.edges:
            raise ValueError('syntax children have wrong typed occurrence outputs')
    @property
    def whole(self):
        return self.generator.image.whole
    @property
    def profile(self):
        return Profile(self.whole.source, self.whole.target,
                       tuple(e for t in self.children for e in t.profile.edges))


def corolla(g):
    return Node(g, tuple(Leaf(r) for r in g.image.profile.edges))


def evaluate(t):
    if isinstance(t, Leaf):
        return singleton(t.whole)
    return substitute(t.generator.image, tuple(evaluate(s) for s in t.children))


def graft(t, replacements):
    replacements = tuple(replacements)
    if tuple(s.whole for s in replacements) != t.profile.edges:
        raise ValueError('graft replacements have wrong ordered leaf outputs')
    it = iter(replacements)
    def go(t):
        if isinstance(t, Leaf):
            return next(it)
        return Node(t.generator, tuple(go(s) for s in t.children))
    result = go(t)
    assert next(it, None) is None
    return result


def rel(source, target, pairs):
    return Relation(source, target, sum(1 << (x*target.size+y) for x,y in set(pairs)))


def profile(edges, at=None):
    edges = tuple(edges)
    if edges:
        return Profile(edges[0].source, edges[-1].target, edges)
    if at is None:
        raise ValueError('nullary interface must be supplied')
    return Profile(at, at, ())


def pair_data(r):
    return {'source': r.source.label, 'target': r.target.label,
            'sizes': [r.source.size, r.target.size], 'mask': r.mask,
            'pairs': [[x,y] for x in range(r.source.size) for y in range(r.target.size)
                      if r.mask & (1 << (x*r.target.size+y))]}


def cell_data(c):
    return {'whole': pair_data(c.whole), 'profile': [pair_data(r) for r in c.profile.edges],
            'boundary_labels': [i.label for i in c.profile.interfaces],
            'composite': pair_data(c.profile.composite), 'exact': c.exact}


def reject(name, f):
    try:
        f()
    except ValueError as e:
        return {'name':name, 'detected':True, 'reason':str(e)}
    raise AssertionError('negative control accepted: '+name)


def named_checks():
    a,b,c = Interface('A',2),Interface('B',3),Interface('C',2)
    ap,bp,cp = Interface("A'",2),Interface("B'",2),Interface("C'",2)
    r=rel(a,b,[(0,0),(1,2)]); s=rel(b,c,[(0,0),(2,1)])
    p=profile((r,s)); composite=p.composite
    w=rel(a,c,[(0,0),(1,1),(0,1)])
    exact=exact_cell(composite,p); nonexact=Cell(w,p)
    assert not nonexact.exact and composite.mask != 0
    f=InterfaceMap(ap,a,(0,1)); g=InterfaceMap(bp,b,(0,1)); h=InterfaceMap(cp,c,(0,1))
    restricted=restrict_cell(exact,(f,g,h))
    assert restricted.profile.composite.mask == 1
    assert restricted.whole.mask == 9 and not restricted.exact
    assert restrict_cell(nonexact,(f,g,h)).whole.mask == 11
    # The realizer map removes the original (1,2,1) but keeps (0,0,0).
    oldreal=realizers((2,3,2),(r.mask,s.mask))
    newreal=realizers((2,2,2),tuple(x.mask for x in restricted.profile.edges))
    images=tuple((f.values[x],g.values[y],h.values[z]) for x,y,z in newreal)
    assert set(images) < set(oldreal)
    bpp=Interface('Bsurj',4); gs=InterfaceMap(bpp,b,(0,1,2,2))
    positive=restrict_cell(exact,(f,gs,h)); assert positive.exact
    apos=Interface('Adup',3); cpos=Interface('Cdup',3)
    fd=InterfaceMap(apos,a,(0,0,1)); hd=InterfaceMap(cpos,c,(0,1,1))
    many=restrict_cell(exact,(fd,gs,hd)); assert many.exact
    surjreal=realizers((2,4,2),tuple(x.mask for x in positive.profile.edges))
    surjimage=tuple((f.values[x],gs.values[y],h.values[z]) for x,y,z in surjreal)
    assert len(set(surjimage)) < len(surjimage)  # actual map need not inject
    # Identity and composite restriction, using maps at every original label.
    app=Interface("A''",3); bpp2=Interface("B''",1); cpp=Interface("C''",3)
    f2=InterfaceMap(app,ap,(0,1,1)); g2=InterfaceMap(bpp2,bp,(0,)); h2=InterfaceMap(cpp,cp,(1,0,1))
    twice=restrict_cell(restricted,(f2,g2,h2))
    once=restrict_cell(exact,(f.after(f2),g.after(g2),h.after(h2)))
    assert twice == once
    ids=tuple(InterfaceMap(i,i,tuple(range(i.size))) for i in p.interfaces)
    assert restrict_cell(nonexact,ids) == nonexact
    # Four-leaf typed syntax, two identical nonempty loop components.
    loop=Relation(b,b,(1 << 9)-1); unit=Relation(b,b,diagonal(3))
    path4=profile((r,loop,loop,s)); whole4=path4.composite
    def binary(name,left,right):
        p0=profile((left.whole,right.whole))
        return Node(Generator(name,exact_cell(p0.composite,p0)),(left,right))
    lr,ll,ls=Leaf(r),Leaf(loop),Leaf(s)
    left=binary('left_root',binary('left_middle',binary('left_bottom',lr,ll),ll),ls)
    right=binary('right_root',lr,binary('right_middle',ll,binary('right_bottom',ll,ls)))
    assert left != right and left.profile == right.profile == path4
    assert evaluate(left) == evaluate(right) == exact_cell(whole4,path4)
    first=corolla(Generator('first_occurrence',exact_cell(loop,profile((unit,loop)))))
    second=corolla(Generator('second_occurrence',exact_cell(loop,profile((loop,unit)))))
    assert first != second and first.whole == second.whole == loop
    refined=graft(right,(lr,first,second,ls))
    repeated_mutant=graft(right,(lr,first,first,ls))
    swapped=graft(right,(lr,second,first,ls))
    assert evaluate(refined) != evaluate(repeated_mutant)
    assert evaluate(refined) != evaluate(swapped)
    # Cell units and a genuine nested simultaneous substitution associativity.
    outer=evaluate(right); children=(singleton(r),evaluate(first),evaluate(second),singleton(s))
    assert substitute(outer,tuple(singleton(x) for x in outer.profile.edges)) == outer
    assert substitute(singleton(whole4),(outer,)) == outer
    mid=substitute(outer,children)
    assert mid == evaluate(refined)
    bottom=tuple(singleton(x) for x in mid.profile.edges)
    # Nontrivial bottom replacement on the first unit loop by an exact nullary.
    nullunit=exact_cell(unit,profile((),at=b))
    bottom=list(bottom); bottom[1]=nullunit; bottom=tuple(bottom)
    cursor=0; composed=[]
    for child in children:
        n=len(child.profile.edges)
        composed.append(substitute(child,bottom[cursor:cursor+n])); cursor+=n
    assert substitute(mid,bottom) == substitute(outer,tuple(composed))
    alpha=Generator('alpha',exact_cell(loop,profile((loop,loop))))
    beta=Generator('beta',alpha.image)
    assert corolla(alpha) != corolla(beta) and evaluate(corolla(alpha)) == evaluate(corolla(beta))
    # Same boundary choices on the whole forest; arbitrary restricted cells survive.
    fam={a:f,b:g,c:h}
    restricted_subst=restrict_family(substitute(outer,children),fam)
    subst_restricted=substitute(restrict_family(outer,fam),tuple(restrict_family(x,fam) for x in children))
    assert restricted_subst == subst_restricted
    # Nullary containment is not a unit assertion about arbitrary loop relations.
    nullcontain=Cell(loop,profile((),at=b)); assert not nullcontain.exact
    one=Interface('One',1); two=Interface('Two',2)
    delta1=Relation(one,one,diagonal(1)); null1=exact_cell(delta1,profile((),at=one))
    constant=InterfaceMap(two,one,(0,0)); nullpull=restrict_cell(null1,(constant,))
    assert nullpull.whole.mask == 15 and nullpull.profile.composite.mask == 9 and not nullpull.exact
    # Empty domains show why naive converses need exceptions.
    empty=Interface('Empty',0); e_to_a=InterfaceMap(empty,a,())
    empty_endpoint=restrict_cell(exact,(e_to_a,g,h)); assert empty_endpoint.exact
    r0=Relation(a,empty,0); s0=Relation(empty,c,0)
    empty_mid=exact_cell(Relation(a,c,0),profile((r0,s0)))
    assert empty_mid.exact
    eunit=exact_cell(Relation(empty,empty,0),profile((),at=empty)); assert eunit.exact
    # Invalid semantic/syntax constructions and deliberate mutations.
    controls=[
      reject('reverse containment would accept composite not contained in W',lambda:Cell(Relation(a,c,0),p)),
      reject('nonexact whole cannot be asserted exact',lambda:exact_cell(w,p)),
      reject('nullary nonloop',lambda:Cell(r,profile((),at=a))),
      reject('reversed ordered profile',lambda:profile((s,r))),
      reject('wrong repeated occurrence output',lambda:graft(right,(lr,lr,second,ls))),
      reject('wrong endpoints in restriction map',lambda:restrict_relation(r,h,g)),
      reject('equal cardinalities are not equal interface labels',lambda:Profile(a,c,())),
      reject('nullary gluing with two independent boundary maps',lambda:restrict_cell(nullunit,(g,g))),
      reject('false exactness after non-surjective restriction',lambda:exact_cell(restricted.whole,restricted.profile)),
    ]
    controls += [
      {'name':'conflate composite of pulls with pull of composite','detected':True,
       'correct_mask':restricted.profile.composite.mask,'mutant_mask':restricted.whole.mask},
      {'name':'identify repeated component occurrences','detected':True,
       'correct_profile':[x.mask for x in evaluate(refined).profile.edges],
       'mutant_profile':[x.mask for x in evaluate(repeated_mutant).profile.edges]},
      {'name':'empty composite is empty relation rather than diagonal','detected':True,
       'correct_mask':nullunit.profile.composite.mask,'mutant_mask':0},
      {'name':'nullary exactness from vacuous internal surjectivity','detected':True,
       'correct_composite':nullpull.profile.composite.mask,'pulled_whole':nullpull.whole.mask},
    ]
    return {
      'status':'PASS','F4':{'original_exact':cell_data(exact),'strict_containment':cell_data(nonexact),
       'non_surjective_boundary':{'values':list(g.values),'original_size':3,'new_size':2,
        'old_realizers':oldreal,'new_realizers':newreal,'mapped_realizers':images,
        'restricted_original_exact':cell_data(restricted)},
       'surjective_many_to_one':{'values':list(gs.values),'cell':cell_data(positive),
        'realizer_count':len(surjreal),'image_count':len(set(surjimage))},
       'noninjective_endpoints':cell_data(many),'iterated_restriction_equal':True,
       'empty_endpoint':cell_data(empty_endpoint),'empty_intermediate':cell_data(empty_mid)},
      'F5':{'four_leaf':cell_data(outer),'groupings_distinct':True,'groupings_evaluate_equal':True,
       'refined':cell_data(evaluate(refined)),'first_replacement':cell_data(evaluate(first)),
       'second_replacement':cell_data(evaluate(second)),'parallel_primitive_labels':['alpha','beta'],
       'primitive_syntax_distinct_semantics_equal':True,'nested_substitution_associative':True,
       'restriction_substitution_commutes_with_global_incidence':True,
       'nullary_exact':cell_data(nullunit),'nullary_nonexact':cell_data(nullcontain),
       'nullary_noninjective_pull':cell_data(nullpull),'empty_nullary':cell_data(eunit)},
      'F6':controls}


def exhaustive_f1():
    counts=Counter()
    for a,b,c in product(SIZES,repeat=3):
        for r,s in product(masks(a,b),masks(b,c)):
            original=join(a,b,c,r,s)
            assert original == global_chain((a,b,c),(r,s))
            counts['original_relation_pairs']+=1
            for ap,bp,cp in product(SIZES,repeat=3):
                counts['size_six_tuples_per_relation_pair']+=1
                for f,g,h in product(functions(ap,a),functions(bp,b),functions(cp,c)):
                    counts['comparison_cases']+=1
                    rp=pull(a,b,r,f,g); sp=pull(b,c,s,g,h)
                    composed=join(ap,bp,cp,rp,sp)
                    pulled=pull(a,c,original,f,h)
                    assert composed & ~pulled == 0
                    assert composed == global_chain((ap,bp,cp),(rp,sp))
                    onto=len(set(g)) == b
                    if onto:
                        assert composed == pulled
                        counts['surjective_intermediate_cases']+=1
                    if composed != pulled:
                        counts['strict_comparison_cases']+=1
                    if ap==0 or cp==0:
                        counts['empty_endpoint_cases']+=1
                    if b==0:
                        counts['empty_original_intermediate_cases']+=1
                    for xs in realizers((ap,bp,cp),(rp,sp)):
                        ys=(f[xs[0]],g[xs[1]],h[xs[2]])
                        assert ys in realizers((a,b,c),(r,s))
                        counts['realizer_map_checks']+=1
                    for w in supersets(original,a,c):
                        pw=pull(a,c,w,f,h)
                        assert composed & ~pw == 0
                        counts['containment_cell_restrictions']+=1
                        if w!=original:
                            counts['original_nonexact_cells']+=1
                        if composed==pw:
                            counts['restricted_exact_cells']+=1
                        else:
                            counts['restricted_nonexact_cells']+=1
    return {'status':'PASS','counts':dict(sorted(counts.items()))}


def exhaustive_f2():
    counts=Counter()
    for a,b in product(SIZES,repeat=2):
        for r in masks(a,b):
            assert join(a,a,b,diagonal(a),r)==r
            assert join(a,b,b,r,diagonal(b))==r
            assert global_chain((a,a,b),(diagonal(a),r))==r
            assert global_chain((a,b,b),(r,diagonal(b)))==r
            counts['unit_equalities_per_evaluator']+=2
    for a,b,c,d in product(SIZES,repeat=4):
        for r,s,t in product(masks(a,b),masks(b,c),masks(c,d)):
            lhs=join(a,c,d,join(a,b,c,r,s),t)
            rhs=join(a,b,d,r,join(b,c,d,s,t))
            oracle=global_chain((a,b,c,d),(r,s,t))
            assert lhs==rhs==oracle
            counts['associativity_triples']+=1
            if 0 in (a,b,c,d): counts['triples_with_empty_interface']+=1
    return {'status':'PASS','counts':dict(sorted(counts.items()))}

@lru_cache(None)
def segment_lengths(n,k):
    if k==0:
        return ((),) if n==0 else ()
    return tuple(xs for xs in product(range(n+1),repeat=k) if sum(xs)==n)


def exhaustive_f3():
    counts=Counter(); arities=Counter()
    for n in range(4):
        for dims in product(SIZES,repeat=n+1):
            for rs in product(*(masks(dims[i],dims[i+1]) for i in range(n))):
                flat=chain(dims,rs)
                assert flat==global_chain(dims,rs)
                counts['flat_profiles']+=1
                for k in range(4):
                    for lengths in segment_lengths(n,k):
                        cuts=[0]
                        for length in lengths: cuts.append(cuts[-1]+length)
                        assert cuts[-1]==n
                        outer_dims=tuple(dims[j] for j in cuts)
                        composites=tuple(chain(dims[cuts[i]:cuts[i+1]+1],rs[cuts[i]:cuts[i+1]]) for i in range(k))
                        assert chain(outer_dims,composites)==flat
                        assert global_chain(outer_dims,composites)==flat
                        counts['profile_segmentations']+=1
                        counts['exact_substitutions']+=1
                        counts['nullary_inner_segments']+=lengths.count(0)
                        arities[str(k)]+=1
                        choices=tuple(supersets(composites[i],outer_dims[i],outer_dims[i+1]) for i in range(k))
                        for outer_rs in product(*choices):
                            middle=chain(outer_dims,outer_rs)
                            assert flat & ~middle==0
                            counts['inner_whole_families']+=1
                            for whole in supersets(middle,dims[0],dims[-1]):
                                assert flat & ~whole==0
                                counts['containment_substitutions']+=1
                                if whole!=middle: counts['nonexact_outer_cells']+=1
                                if whole!=flat: counts['nonexact_composite_cells']+=1
    return {'status':'PASS','counts':dict(sorted(counts.items())),
            'segmentations_by_outer_arity':dict(sorted(arities.items()))}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    parser.add_argument('--named-only',action='store_true',help='smoke only; does not claim exhaustive F1–F3')
    args=parser.parse_args()
    here=Path(__file__).resolve(); target=here.parent.parent/'C2_Targets.md'
    assert hashlib.sha256(target.read_bytes()).hexdigest()==TARGET_SHA256
    report={'schema':'C2-finite-author-v1','evidence':'C; finite computation, not kernel proof',
            'contract_sha256':CONTRACT_SHA256,'target_sha256':TARGET_SHA256,
            'source_sha256':hashlib.sha256(here.read_bytes()).hexdigest(),
            'scope':'C2 local author evidence; full C2 remains OPEN pending D2/E use',
            'named':named_checks()}
    for name,run in [('F1',exhaustive_f1),('F2',exhaustive_f2),('F3',exhaustive_f3)]:
        if args.named_only:
            report[name]={'status':'NOT RUN'}
        else:
            start=time.monotonic(); report[name]=run()
            print(json.dumps({'stage':name,'seconds':round(time.monotonic()-start,3),**report[name]}),flush=True)
    report['status']='NAMED ONLY' if args.named_only else 'PASS; AUTHOR TESTED, INDEPENDENT REVIEW REQUIRED'
    data=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(data)
        print(json.dumps({'output':str(args.output),'sha256':hashlib.sha256(data.encode()).hexdigest(),'status':report['status']}))
    else:
        print(data)

if __name__=='__main__':
    main()
