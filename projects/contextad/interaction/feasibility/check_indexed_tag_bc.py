#!/usr/bin/env python3
"""Exact pullback/substitution control for indexed list-labelled tags."""
from itertools import product
from fractions import Fraction
from collections import defaultdict
import json

B = ('b',)
X = (0,1)
f = {0:'b',1:'b'}
Q = {'q':('b','b'), 'z':()}
T = {
    'repeat':(('Q','q'),('Q','q')),
    'mixed':(('Q','z'),('Q','q'),('Q','z'),('Q','q'),('Q','z')),
    'emptytags':(('Q','z'),('Q','z')),
    'nil':(),
    'base':(('B','b'),('Q','q'),('Q','z'),('B','b')),
}

def lifts(word,base_map,domain):
    return [xs for xs in product(domain,repeat=len(word))
            if tuple(base_map[x] for x in xs)==word]

def flat(word):
    return tuple(b for kind,key in word for b in ((key,) if kind=='B' else Q[key]))

def split_lift(word,xs):
    pos=0
    result=[]
    for kind,key in word:
        n=1 if kind=='B' else len(Q[key])
        chunk=xs[pos:pos+n]
        pos+=n
        result.append(('X',chunk[0]) if kind=='B' else ('Qhat',(key,chunk)))
    assert pos==len(xs)
    return tuple(result)

def flatten_lift(word):
    return tuple(x for kind,val in word for x in ((val,) if kind=='X' else val[1]))

qhat = tuple((q,xs) for q,word in Q.items() for xs in lifts(word,f,X))
DFdomain = tuple(('X',x) for x in X)+tuple(('Qhat',qx) for qx in qhat)
df = {a:(('B',f[a[1]]) if a[0]=='X' else ('Q',a[1][0])) for a in DFdomain}

counts={}
for t,word in T.items():
    lhs=set(lifts(flat(word),f,X))
    rhs=set(lifts(word,df,DFdomain))
    assert {split_lift(word,xs) for xs in lhs}==rhs
    assert {flatten_lift(ys) for ys in rhs}==lhs
    for xs in lhs: assert flatten_lift(split_lift(word,xs))==xs
    for ys in rhs: assert split_lift(word,flatten_lift(ys))==ys
    counts[t]={'flattened_arity':len(flat(word)),'lhs':len(lhs),'rhs':len(rhs)}

# Repeated occurrences of q lift independently, not as one shared q lift.
repeat_word=T['repeat']
lift=split_lift(repeat_word,(0,0,1,1))
assert lift[0] != lift[1]
assert df[lift[0]]==df[lift[1]]==('Q','q')

# Naturality with respect to a noninjective map g:X->Y: relabel each retained
# coordinate before or after the canonical split.
g={0:'y',1:'y'}
def map_lift(ys):
    return tuple(('X',g[v]) if k=='X' else ('Qhat',(v[0],tuple(g[x] for x in v[1])))
                 for k,v in ys)
for t,word in T.items():
    for xs in lifts(flat(word),f,X):
        assert map_lift(split_lift(word,xs))==split_lift(word,tuple(g[x] for x in xs))

# Two equal-label tags merge, while independent context cells take parity.
tags=('a','c')
tag_map={'a':'merged','c':'merged'}
source_tuples=tuple(product(range(4),repeat=2))
target_tuples=set(product(range(2),repeat=2))
source_qhat={(q,rs) for q in tags for rs in source_tuples}
def lift_cell(qrs):
    q,rs=qrs
    return (tag_map[q],tuple(r%2 for r in rs))
target_qhat={('merged',rs) for rs in target_tuples}
assert {lift_cell(qrs) for qrs in source_qhat}==target_qhat
assert len(source_qhat)==32 and len(target_qhat)==4
assert lift_cell(('a',(0,1)))==lift_cell(('c',(2,3)))
for q in tags:
    mass=defaultdict(Fraction)
    for rs in source_tuples: mass[tuple(r%2 for r in rs)]+=Fraction(1,16)
    assert dict(mass)=={rs:Fraction(1,4) for rs in target_tuples}

def chi_source(tagged):
    kind,val=tagged
    return ('value',('b',val)) if kind=='B' else ('tag',val)
def left_cell(tagged):
    kind,val=tagged
    return ('B',val%2) if kind=='B' else ('Q',lift_cell(val))
def right_cell(output):
    kind,val=output
    return ('value',(val[0],val[1]%2)) if kind=='value' else ('tag',lift_cell(val))
def chi_target(tagged):
    kind,val=tagged
    return ('value',('b',val)) if kind=='B' else ('tag',val)
source_extension=[('B',r) for r in range(4)]+[('Q',qx) for qx in source_qhat]
for x in source_extension:
    assert right_cell(chi_source(x))==chi_target(left_cell(x))
assert len(source_extension)==36

print(json.dumps({'status':'passed','qhat_points':len(qhat),
 'tag_composite_pullback_points':len(qhat)+sum(c['lhs'] for c in counts.values()),
 'tests':counts,
 'indexed_grade_cell_test':{'source_decorated_tags':len(source_qhat),
    'target_decorated_tags':len(target_qhat),'checked_square_points':len(source_extension),
    'conditional_pushforward':'uniform16 to uniform4 for each source tag',
    'noninvertible_maps':['tag merge','coordinatewise parity']},
 'scope':'exact finite controls of canonical splitting; not full interaction theorem'},indent=2))
