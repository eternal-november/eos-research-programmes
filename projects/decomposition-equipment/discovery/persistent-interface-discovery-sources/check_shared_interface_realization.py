import itertools,json,math
from pathlib import Path

def span(vs):
    s={0}
    for v in vs:s|={x^v for x in list(s)}
    return frozenset(s)
def join(a,b):return span(a|b)
def lattice(ws):
    l=set(ws)|{frozenset({0}),join_all(ws)}
    while True:
        old=len(l)
        for a,b in itertools.product(list(l),repeat=2):l.add(a&b);l.add(join(a,b))
        if len(l)==old:return l
def join_all(ws):return span(set().union(*ws))
subs={span(vs) for r in range(4) for vs in itertools.combinations(range(1,8),r)}
bases=[b for b in itertools.combinations(range(1,8),3) if len(span(b))==8]
count=0
for ws in itertools.combinations(subs,3):
    V=join_all(ws)
    Bs=[b for r in range(4) for b in itertools.combinations(V-{0},r) if len(span(b))==len(V) and 2**r==len(V)]
    adapted=next((b for b in Bs if all(span([x for x in b if x in w])==w for w in ws)),None)
    l=lattice(ws)
    dist=all(x&join(y,z)==join(x&y,x&z) for x,y,z in itertools.product(l,repeat=3))
    assert (adapted is not None)==dist
    count+=1
# Every invariant arrangement's adapted basis has overlap-local shift coefficients.
shift_checks=0
for b in bases:
    ws=[span(b[:2]),span(b[1:]),span(b[1:2])]
    for images in itertools.product(range(8),repeat=3):
        def T(x):
            y=0
            for i in range(3):
                if x>>i&1:y^=images[i]
            return y
        if not all(all(T(x) in w for x in w) for w in ws):continue
        for v in b:
            readers=[w for w in ws if v in w]
            common=[c for c in b if all(c in w for w in readers)]
            assert T(v) in span(common)
        shift_checks+=1
codes=0
for d in range(1,9):
    for b in range(1,d+1):
        blocks=[list(range(j,d,b)) for j in range(b)]
        regs=set()
        for block in blocks:
            regs|={sum((1<<block[j]) for j in range(len(block)) if m>>j&1) for m in range(1,1<<len(block))}
        for query in range(1,1<<d):
            chosen=[query & sum(1<<j for j in block) for block in blocks]
            chosen=[v for v in chosen if v]
            assert len(chosen)<=b and all(v in regs and v&query==v for v in chosen)
            v=0
            for w in chosen:v^=w
            assert v==query
        assert len(regs)<=b*(2**math.ceil(d/b)-1)
        codes+=1
out=dict(F2_dim3_arrangements=count,invariant_shift_checks=shift_checks,block_parity_cases=codes,all_passed=True)
Path(__file__).with_name('Shared_Interface_QA.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
# Nonlinear saturated-register theorem: all encoders of extra-history states,
# and all bijections of the four demand values in the diamond.
saturated=0
for encoding in itertools.product(range(4),repeat=8):
    decoder={};valid=True
    for h,word in enumerate(encoding):
        x=h//2
        if word in decoder and decoder[word]!=x:valid=False;break
        decoder[word]=x
    if valid:
        assert all(encoding[2*x]==encoding[2*x+1] for x in range(4))
        assert len({encoding[2*x] for x in range(4)})==4
        saturated+=1
assert saturated==24
for encoding in itertools.permutations(range(4)):
    locally_realized=[]
    for form in [1,2,3]:
        def demand(x):return (x&form).bit_count()%2
        possible=any(all((((encoding[x]>>j)&1)==((encoding[y]>>j)&1)) == (demand(x)==demand(y)) for x in range(4) for y in range(4)) for j in range(2))
        locally_realized.append(possible)
    assert not all(locally_realized)
print({'nonlinear_extra_history_encoders_checked':4**8,'saturated_valid_encoders':saturated,'diamond_bijections_excluded':24})
out.update(nonlinear_extra_history_encoders_checked=4**8,saturated_valid_encoders=saturated,diamond_bijections_excluded=24)
Path(__file__).with_name('Shared_Interface_QA.json').write_text(json.dumps(out,indent=2)+'\n')
