"""Finite diagnostic only: proof remains structural, not inferred from counts."""
from itertools import product
# A primitive shape is (arity, slots); slots are None (external) or (color, tree).
def trees(depth):
    options=[None]
    if depth: options += [(c,t) for c in ('U','V') for t in trees(depth-1)]
    return [(n,s) for n in range(3) for s in product(options,repeat=n)]
def ext(t): return sum(1 if s is None else ext(s[1]) for s in t[1])
# Target primitive node: tuple of (decoration, final slots).
# decoration ('I',) is bypass; ('D',arity) is a genuine terminal shape.
def fusion_then_post(t,ds):
    out=[]
    for s in t[1]:
        if s is None:
            d=next(ds); out.append((('D',d),(None,)*d))
        else:
            c,ch=s;out.append((('I',),((c,fusion_then_post(ch,ds)),)))
    return tuple(out)
# Cut U edges: each outer node has a V component with U slots holding outer children.
def cut_u(t):
    def component(t):
        ss=[]
        for s in t[1]:
            if s is None:ss.append(('leaf',None))
            elif s[0]=='V':ss.append(('V',component(s[1])))
            else:ss.append(('U',cut_u(s[1])))
        return tuple(ss)
    return component(t)
# Outer post-tightening puts bypasses at U slots, D at external leaves.
def outer_post(comp,ds):
    result=[]
    for tag,ch in comp:
        if tag=='V':result.append(('V',outer_post(ch,ds)))
        elif tag=='U':result.append(('decor',('I',),('U',outer_post(ch,ds))))
        else:result.append(('decor',('D',next(ds)),None))
    return tuple(result)
# h inserts bypasses at V internal edges, preserving supplied D/I leaves.
def normalize_h(comp):
    out=[]
    for slot in comp:
        if slot[0]=='V':out.append((('I',),(('V',normalize_h(slot[1])),)))
        else:
            _,d,ch=slot
            out.append((d,(None,)*d[1] if d[0]=='D' else (('U',normalize_h(ch[1])),)))
    return tuple(out)
count=0
for t in trees(1):
    for ds in product(range(3),repeat=ext(t)):
        assert fusion_then_post(t,iter(ds))==normalize_h(outer_post(cut_u(t),iter(ds)))
        count+=1
print(f'PASS: {len(trees(1))} mixed C trees; {count} complete D-decoration assignments; D arities 0,1,2.')
print('C root plus at most one recursive C level; all U/V edge choices. Finite diagnostic, not general proof.')
