"""Finite B / cluster quotient evidence. Python standard library, no proof by tests."""
from itertools import product
from collections import Counter, defaultdict
from math import prod


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def tuples(spans):
    out = [()]
    for span in spans:
        out = [prefix + (x,) for prefix in out for x in span
               if not prefix or prefix[-1][2] == x[1]]
    return out


def reindex(span, left, right):
    return [((a, x[0], b), a, b) for x in span
            for a, fa in enumerate(left) for b, fb in enumerate(right)
            if fa == x[1] and fb == x[2]]


def boundary_check(spans, fs):
    """Compare actual c_f fibres with internal-lift product, not cardinalities only."""
    old = tuples(spans)
    target = [(a, tuple(x[0] for x in xs), b) for xs in old
              for a, fa in enumerate(fs[0]) for b, fb in enumerate(fs[-1])
              if fa == xs[0][1] and fb == xs[-1][2]]
    source = tuples([reindex(s, fs[i], fs[i+1]) for i, s in enumerate(spans)])
    counts = Counter((xs[0][1], tuple(x[0][1] for x in xs), xs[-1][2]) for xs in source)
    expected = {}
    for xs in old:
        lifts = prod(sum(v == xs[i][2] for v in fs[i+1]) for i in range(len(spans)-1))
        for a, fa in enumerate(fs[0]):
            for b, fb in enumerate(fs[-1]):
                if fa == xs[0][1] and fb == xs[-1][2]:
                    key = (a, tuple(x[0] for x in xs), b)
                    expected[key] = lifts
    require(set(counts) <= set(target), 'c_f not a total map into target')
    require(all(counts[k] == expected[k] for k in target), 'lift product differs from enumerated fibre')
    return {'source_size': len(source), 'target_size': len(target),
            'fibre_sizes': [counts[k] for k in target],
            'bijective': all(counts[k] == 1 for k in target)}


def compositions(n, k):
    if k == 1:
        yield (n,)
    else:
        for first in range(n+1):
            for tail in compositions(n-first, k-1):
                yield (first,) + tail


def chain(support):
    return not any(i < k and j > l for i, j in support for k, l in support)


def support(table, rows, cols):
    return {(i,j) for i in range(rows) for j in range(cols) if table[i*cols+j]}


def marginals(table, rows, cols):
    return (tuple(sum(table[i*cols+j] for j in range(cols)) for i in range(rows)),
            tuple(sum(table[i*cols+j] for i in range(rows)) for j in range(cols)))


def interval_table(a, b):
    out = []
    lo = 0
    for x in a:
        lj = 0
        for y in b:
            out.append(max(0, min(lo+x, lj+y)-max(lo, lj)))
            lj += y
        lo += x
    return tuple(out)


def run():
    # Optimization cannot remove these require checks. Caller must also run without -O.
    require(__debug__, 'Optimization forbidden: rerun Python without -O / PYTHONOPTIMIZE')
    relations = []
    pairs = list(product(range(2), repeat=2))
    for mask in range(16):
        relations.append([(i,a,b) for i,(a,b) in enumerate(pairs) if mask >> i & 1])
    maps = [p for n in range(3) for p in product(range(2), repeat=n)]
    comparisons = fibres = 0
    for left, right in product(relations, repeat=2):
        for fs in product(maps, repeat=3):
            result = boundary_check([left,right], fs)
            comparisons += 1
            fibres += result['target_size']
    nullary = []
    for f in maps:
        target = [(a,b) for a in range(len(f)) for b in range(len(f)) if f[a] == f[b]]
        diagonal = [(a,a) for a in range(len(f))]
        good = len(set(f)) == len(f)
        require((set(target) == set(diagonal)) == good, 'nullary injectivity criterion')
        nullary.append({'map': list(f), 'source_size':len(diagonal), 'target_size':len(target), 'bijective':good})
    # Every old path goes through value 1, while both new internal interfaces only map to 0.
    path = [[('s',0,1)], [('t',1,1)], [('u',1,0)]]
    fs = [(0,), (0,), (0,), (0,)]
    adjacent = [boundary_check(path[i:i+2],fs[i:i+3]) for i in range(2)]
    full = boundary_check(path,fs)
    require(all(x['bijective'] and x['target_size']==0 for x in adjacent), 'adjacent vacuity')
    require(full['target_size']==1 and full['fibre_sizes']==[0] and not full['bijective'], 'full missing lift')
    # Active whole graph has cross-edge 1--3; proper induced {1,2} is inactive.
    # Whole's declared support quotient collapses witness lifts, not the proper carrier.
    simple = [[('s',0,0)], [('t',0,0)], [('u',0,0)]]
    dup = [(0,), (0,0), (0,), (0,)]
    intermediate = boundary_check(simple[:2],dup[:3])
    whole = boundary_check(simple,dup)
    whole_source_support = {(0,0)} if whole['source_size'] else set()
    whole_target_support = {(0,0)} if whole['target_size'] else set()
    require(intermediate['fibre_sizes']==[2] and whole_source_support==whole_target_support,
            'support quotient masking control')
    # Bijections on raw witness sets covering noninjective boundary map are not W maps.
    old = [[(0,0,0),(1,0,0)],[(0,0,0),(1,0,0)]]
    new = [[(0,0,0),(1,0,1)],[(0,0,0),(1,1,0)]]
    old_tuples, new_tuples = tuples(old), tuples(new)
    pullbacks = [reindex(old[0],(0,),(0,0)),reindex(old[1],(0,0),(0,))]
    hbars = [[(x[1],x[0],x[2]) for x in s] for s in new]
    require(len(old_tuples)==4 and len(new_tuples)==2, 'raw apex maps composite sizes')
    require(all(len(s)==4 for s in pullbacks) and all(len(s)==2 for s in hbars), 'h_bar failure')
    hbar_fibres = []
    for actual, pb in zip(hbars, pullbacks):
        target_ids = [x[0] for x in pb]
        require(set(actual) <= set(target_ids), 'h_bar not a total fixed-interface map')
        counts = Counter(actual)
        hbar_fibres.append([counts[x] for x in target_ids])
    require(all(sorted(f)==[0,0,1,1] for f in hbar_fibres), 'h_bar fibre control')
    growth = []
    for n in range(1,13):
        # All repeated singleton spans are separate named occurrences.
        spans = [[('occ%d'%i,0,0)] for i in range(n)]
        for multiplicity in (0,1,2,3):
            fs = [(0,)] + [tuple(0 for _ in range(multiplicity)) for _ in range(n-1)] + [(0,)]
            # Explicit enumeration limit prevents exponential runaway.
            if multiplicity ** max(0,n-1) > 100000:
                continue
            result = boundary_check(spans, fs)
            require(result['fibre_sizes']==[multiplicity**(n-1)], 'growth formula')
            growth.append({'arity':n,'internal_lift_multiplicity':multiplicity,**result})
    # Independently enumerate ALL integer tables of fixed total; do not generate using interval formula.
    table_count = marginal_count = 0
    dimensions = []
    for rows, cols in product(range(1,4), repeat=2):
        dim_tables = dim_marginals = 0
        for mass in range(6):
            candidates = defaultdict(list)
            for table in compositions(mass,rows*cols):
                candidates[marginals(table,rows,cols)].append(table)
                table_count += 1
                dim_tables += 1
            for a,b in product(compositions(mass,rows),compositions(mass,cols)):
                actual = [t for t in candidates[(a,b)] if chain(support(t,rows,cols))]
                expected = interval_table(a,b)
                require(actual == [expected], 'single-clique chain uniqueness or interval formula')
                marginal_count += 1
                dim_marginals += 1
        dimensions.append({'rows':rows,'columns':cols,'integer_tables':dim_tables,'marginal_pairs':dim_marginals})
    multi_count = multi_table_count = 0
    multi_failure_example = None
    for mass1,mass2 in product(range(3),repeat=2):
        def options(mass):
            d=defaultdict(list)
            for t in compositions(mass,4):
                d[marginals(t,2,2)].append(t)
            return d
        d1,d2=options(mass1),options(mass2)
        for (a1,b1), (a2,b2) in product(d1,d2):
            actual=[]
            for t1,t2 in product(d1[(a1,b1)],d2[(a2,b2)]):
                multi_table_count += 1
                if chain(support(t1,2,2)|support(t2,2,2)):
                    actual.append((t1,t2))
            c1,c2=interval_table(a1,b1),interval_table(a2,b2)
            expected=[(c1,c2)] if chain(support(c1,2,2)|support(c2,2,2)) else []
            require(actual==expected, 'union-support theorem B mismatch')
            multi_count += 1
            if not expected and multi_failure_example is None:
                multi_failure_example={'marginals':[[a1,b1],[a2,b2]],'interval_tables':[c1,c2]}
    actual_k2={(0,1),(1,0)}
    orbit_k2=interval_table((1,1),(1,1))
    require(not chain(actual_k2) and orbit_k2==(1,0,0,1),'K2 representative distinction')
    return {
      'boundary':{'exhaustive_domain':'All 16 binary endpoint-support relations per span (one named witness per occupied pair), all pairs of spans, all 7 functions from carriers of size 0..2 to {0,1} independently at three interfaces.',
       'comparisons':comparisons,'target_fibres_checked':fibres,'nullary':nullary,
       'adjacent_pair_vacuity':{'spans':path,'interface_maps':[(0,),(0,),(0,),(0,)],'adjacent':adjacent,'full':full},
       'whole_support_mask':{'graph_vertices':[1,2,3],'graph_edges':[[1,3]],'inactive_proper_vertices':[1,2], 'intermediate':intermediate,'whole_actual':whole,'whole_support_quotient_bijective':True,'quotient_scope':'Explicit endpoint-support quotient at whole only; no claim actual whole c_f is bijective.'},
       'covering_apex_bijection_is_not_fixed_interface_W':{'old_spans':old,'new_spans':new,'boundary_maps':[(0,),(0,0),(0,)],'raw_apex_maps':[[(0,0),(1,1)],[(0,0),(1,1)]],'old_composite_size':4,'new_composite_size':2,'fixed_interface_h_bar_domain_sizes':[2,2],'fixed_interface_h_bar_target_sizes':[4,4],'fixed_interface_h_bar_images':hbars,'fixed_interface_h_bar_targets':[[x[0] for x in s] for s in pullbacks],'fixed_interface_h_bar_fibres':hbar_fibres,'W_pass':False},
       'growth_samples':growth,'enumeration_guard':'Skip sample iff predicted explicit source tuples exceed 100000; all listed samples explicitly enumerated.'},
      'cluster_quotient':{'exhaustive_domain':'One clique: dimensions 1..3 by 1..3, total mass 0..5, all nonnegative integer joint tables and all marginals. Two cliques: each mass 0..2, dimensions 2 by 2, all marginal pairs and all joint-table pairs.',
       'single_clique_tables':table_count,'single_clique_marginal_pairs':marginal_count,'dimensions':dimensions,'two_clique_marginal_cases':multi_count,'two_clique_table_pairs':multi_table_count,'union_support_failure':multi_failure_example,
       'K2':{'actual_U':[[1],[2]],'actual_V':[[2],[1]],'actual_intersection_support':[[0,1],[1,0]],'actual_parallel':False,'orbit_marginals':[[1,1],[1,1]],'orbit_joint':list(orbit_k2),'orbit_parallel':True}},
      'scope':'Finite evidence only. B tests actual boundary composition separately from fixed-interface W. No all-degree theorem inferred.'}

if __name__ == '__main__':
    import json
    print(json.dumps(run(),sort_keys=True,indent=2))
