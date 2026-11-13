"""Independent bounded control, not a proof of A4.
Checks all seven structural rules and all one-step contextual reductions on
terms of <= 7 constructor vertices, two distinct leaf labels, and Z/3 values.
The typed graph proof remains a separate review obligation.
"""
from functools import cache
from itertools import product
import json
from pathlib import Path

MOD = 3
ATOMS = ('u', 'x', 'y')

def C(x,y): return ('c',x,y)
def D(m,x): return ('d',m,x)

@cache
def measure(t):
    if isinstance(t,str): return (0,0,0,0)
    if t[0]=='d':
        b,a,h,d=measure(t[2]); return b,a,h,d+1
    x,y=t[1:]; bx,ax,hx,dx=measure(x); by,ay,hy,dy=measure(y)
    return 1+bx+by, ax+ay+bx, hx+hy+dx+dy, dx+dy

@cache
def evaluation(t):
    if isinstance(t,str): return (() if t=='u' else (t,)),0
    if t[0]=='d':
        p,m=evaluation(t[2]); return p,(m+t[1])%MOD
    p,m=evaluation(t[1]); q,n=evaluation(t[2]); return p+q,(m+n)%MOD

def canonical(t):
    p,m=evaluation(t)
    if not p: c='u'
    else:
        c=p[-1]
        for a in reversed(p[:-1]): c=C(a,c)
    return D(m,c) if m else c

@cache
def steps(t):
    if isinstance(t,str): return ()
    out=[]
    if t[0]=='d':
        m,x=t[1:]
        if m==0: out.append(('D0',x))
        if not isinstance(x,str) and x[0]=='d': out.append(('DA',D((m+x[1])%MOD,x[2])))
        out.extend(('context/'+rule,D(m,z)) for rule,z in steps(x))
    else:
        x,y=t[1:]
        if not isinstance(x,str) and x[0]=='c': out.append(('R',C(x[1],C(x[2],y))))
        if x=='u': out.append(('UL',y))
        if y=='u': out.append(('UR',x))
        if not isinstance(x,str) and x[0]=='d': out.append(('DL',D(x[1],C(x[2],y))))
        if not isinstance(y,str) and y[0]=='d': out.append(('DR',D(y[1],C(x,y[2]))))
        out.extend(('context/'+rule,C(z,y)) for rule,z in steps(x))
        out.extend(('context/'+rule,C(x,z)) for rule,z in steps(y))
    return tuple(out)

@cache
def normal_forms(t):
    ss=steps(t)
    if not ss: return frozenset([t])
    out=set()
    for _,r in ss: out.update(normal_forms(r))
    return frozenset(out)

by_size={1:set(ATOMS)}
for n in range(2,8):
    ts={D(m,t) for t in by_size[n-1] for m in range(MOD)}
    for k in range(1,n-1): ts.update(C(x,y) for x in by_size[k] for y in by_size[n-1-k])
    by_size[n]=ts
counts={}; nsteps=0; nbranch=0
for size,ts in by_size.items():
    counts[size]=len(ts)
    for t in ts:
        ss=steps(t); nsteps+=len(ss); nbranch+=len(ss)>1
        for rule,r in ss:
            assert measure(r)<measure(t),(rule,t,r,measure(t),measure(r))
            assert evaluation(r)==evaluation(t),(rule,t,r)
        assert normal_forms(t)==frozenset([canonical(t)]),(t,normal_forms(t),canonical(t))

# Independent finite check of exact increasing inclusion composition.
restriction_checks=0
for n in range(9):
    for mask in range(1<<n):
        U=tuple(i for i in range(n) if mask>>i&1)
        for vmask in range(1<<len(U)):
            V=tuple(i for i in range(len(U)) if vmask>>i&1)
            composite=tuple(U[j] for j in V)
            image=tuple(sorted(set(composite)))
            assert composite==image
            restriction_checks+=1

result={'kind':'independent_bounded_control','not_an_unrestricted_proof':True,
 'domain':'all terms <=7 vertices; 2 distinct leaf labels; designated nullary; Z/3 decorations',
 'terms_by_size':counts,'total_terms':sum(counts.values()),'contextual_steps':nsteps,
 'branching_terms':nbranch,'all_steps_decrease_lex_measure':True,
 'all_steps_preserve_ordered_leaves_and_value':True,
 'all_reachable_normal_forms_equal_independent_canonical':True,
 'increasing_restriction_compositions_checked':restriction_checks,
 'graph_label_and_interface_calculus_coverage':'not covered by structural term enumeration'}
print(json.dumps(result,indent=2))
Path(__file__).with_name('MixedShapeChecks.json').write_text(json.dumps(result,indent=2)+'\n')

# Mutation-sensitive mixed peak: omitting only DL must be detected.
@cache
def mutant_normal_forms(t):
    ss=[r for rule,r in steps(t) if rule.split('/')[-1]!='DL']
    if not ss: return frozenset([t])
    return frozenset().union(*(mutant_normal_forms(r) for r in ss))
peak=C(C('x',D(1,'y')),'x')
mutant=mutant_normal_forms(peak)
assert len(mutant)==2, mutant
expected=frozenset([C(D(1,C('x','y')),'x'),C('x',C(D(1,'y'),'x'))])
assert mutant==expected,(mutant,expected)
result['deleted_DL_mixed_nonconfluence_detected']=True
result['deleted_DL_peak_normal_forms']=sorted(map(repr,mutant))
Path(__file__).with_name('MixedShapeChecks.json').write_text(json.dumps(result,indent=2)+'\n')
print('Deleted-DL mutation: two distinct irreducibles detected.')
