"""Cross-installation one-cut compatibility; never unions physical edges."""
from hashlib import sha1
from itertools import product
from pathlib import Path
import json,sys

src=Path(sys.argv[1]).resolve()
for ln in Path(__file__).with_name('SOURCE.tsv').read_text().splitlines():
    n,h=ln.split('\t')
    b=(src/n).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
sys.path.insert(0,str(src))
from reuse import Graph,Fact,Observation,full,witnesses,validate_path

def as_graph(specs):
    roots={name for name,_,_ in specs}
    edges={}
    facts={}
    for name,read,action in specs:
        at=name+'-decision'
        edges[name]=frozenset({at})
        edges[at]=frozenset()
        facts[name]=Fact()
        facts[at]=Fact(obs=Observation('admission','next-due',read,action))
    return Graph(frozenset(roots),edges,facts)

def direct(specs):
    keys=sorted({t[1] for t in specs})
    choices=[]
    for values in product(('admit','withhold'),repeat=len(keys)):
        table=dict(zip(keys,values))
        if all(table[k]==p for _,k,p in specs):
            choices.append(table)
    return choices

def audit(specs):
    g=as_graph(specs)
    cache,_=full(g)
    w=witnesses(cache,())['realizability']
    policies=direct(specs)
    assert bool(policies)==(w is None)
    if w:
        assert len(w)==2 and all(validate_path(g,p) for p in w)
        d=[g.facts[p[-1]].obs for p in w]
        assert d[0][:3]==d[1][:3] and d[0].action!=d[1].action
        assert w[0][0]!=w[1][0] # separate worlds, not a spliced path
    return dict(policies=policies,conflicting_rooted_paths=w)

data=json.loads((src/'qualified.json').read_text())
out={}
for key,v in data['variants'].items():
    worlds=[w for z in v.values() for w in z['complete_histories']]
    assert worlds and all(w['old_receipt'] for w in worlds)
    known=lambda h: 'receipt' if h['probe_receipt'] else 'absence'
    prescribe=lambda h: 'admit' if h['next_receipt'] else 'withhold'
    def table(read,policy):
        return [(h['source'],read(h),policy(h)) for h in worlds]
    local=table(known,prescribe)
    assert all(audit([case])['policies'] for case in local)
    out[key]={
        'unqualified_rule_without_read':audit(table(lambda _: 'same accepted plan',prescribe)),
        'actual_matching_probe_read':audit(local),
        'hypothetical_qualified_binding_and_probe':audit(
            table(lambda h:h['binding']+'-'+known(h),prescribe)),
        'conservative_policy':audit(table(known,
            lambda h:'admit' if v[str(h['probe_receipt'])]['judgment']=='carries' else 'withhold')),
        'scope':'Fixed prescribed outcomes; conflict is not nonexistence of safe refusal.',
    }
assert out['next2-dropFalse']['actual_matching_probe_read']['policies']
assert out['next2-dropTrue']['actual_matching_probe_read']['conflicting_rooted_paths']
assert out['next3-dropTrue']['actual_matching_probe_read']['conflicting_rooted_paths']
assert out['next3-dropFalse']['unqualified_rule_without_read']['policies']
assert all(x['hypothetical_qualified_binding_and_probe']['policies'] for x in out.values())
assert all(x['conservative_policy']['policies'] for x in out.values())

comparisons=0
for assignments in product(tuple(product(('r0','r1'),('admit','withhold'))),repeat=4):
    audit([(str(j),*a) for j,a in enumerate(assignments)])
    comparisons+=1
print(json.dumps(dict(scope='prescribed decisions at one authorized actor/cut',
                      cases=out,exact_direct_class_comparisons=comparisons),
                 indent=2,sort_keys=True))
