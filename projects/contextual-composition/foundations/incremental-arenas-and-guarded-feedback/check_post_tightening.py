from itertools import product
import json
# Cnode is tuple of slots; source slot is ('L',Darity) or ('U',child).
# Target slot retains branch tag I/D and outputs (external None/internal tree).
def shapes(depth):
    slots=[('L',m) for m in range(3)]
    if depth:slots += [('U',t) for t in shapes(depth-1)]
    return [ss for n in range(3) for ss in product(slots,repeat=n)]
def forward(t):
    return tuple(('D',(None,)*v) if k=='L' else ('I',(forward(v),)) for k,v in t)
def inverse(t):
    out=[]
    for k,os in t:
        if k=='D':
            assert all(x is None for x in os);out.append(('L',len(os)))
        else:
            assert len(os)==1 and os[0] is not None;out.append(('U',inverse(os[0])))
    return tuple(out)
def arity(t):return sum(sum(1 if x is None else arity(x) for x in os) for _,os in t)
def leftarity(t):return sum(v if k=='L' else leftarity(v) for k,v in t)
ts=shapes(1)
assert all(inverse(forward(t))==t and arity(forward(t))==leftarity(t) for t in ts)
assert len(set(map(forward,ts)))==len(ts)
# Unary C, binary D: a root D with a recursive D child has three leaves.
right=(('D',(None,(('D',(None,None)),))),)
assert arity(right)==3
try:inverse(right);raise RuntimeError('invalid image accepted')
except AssertionError:pass
print(json.dumps({'status':'passed','full_shape_tests':len(ts),'checks':['all-shape-injection','typed-image-inversion','nullary-D-retention','ordered-leaf-count','reverse-arity-obstruction'],'scope':'finite structural diagnostics, not coefficient/coherence certification'},indent=2))
