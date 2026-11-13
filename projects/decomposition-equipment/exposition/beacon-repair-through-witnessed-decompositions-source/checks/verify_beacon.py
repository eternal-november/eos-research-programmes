#!/usr/bin/env python3
"""Independent finite full-witness verifier; no removable Python assertions."""
from itertools import product
import json
B=(0,1)
checks=0

def require(condition, message):
    global checks
    checks += 1
    if not condition:
        raise RuntimeError(message)

def rows(names, predicate):
    return [dict(zip(names,v)) for v in product(B,repeat=len(names)) if predicate(dict(zip(names,v)))]

def key(r):
    return tuple(sorted(r.items()))

def compatible(a,b):
    return all(a[k]==b[k] for k in a.keys() & b.keys())

def glue(rs):
    out={}
    for r in rs:
        require(compatible(out,r), 'inconsistent gluing')
        out.update(r)
    return out

def join(tables):
    return [tuple(rs) for rs in product(*tables) if all(compatible(x,y) for x in rs for y in rs)]

def proj(r,names):
    return {n:r[n] for n in names}

schemas={'N':('g','n'), 'P':('a','n','p'), 'Q':('p','g','y'), 'S':('g','ok')}
physical=(('N','P'),('Q','S'))
functional=(('N','S'),('P','Q'))

def local_tables(eP,eQ):
    return {
      'N':rows(schemas['N'],lambda r:r['n']==1-r['g']),
      'P':rows(schemas['P'],lambda r:r['p']==r['a']*(r['n']^eP)),
      'Q':rows(schemas['Q'],lambda r:r['y']==r['p']*(r['g']^eQ)),
      'S':rows(schemas['S'],lambda r:r['ok']==1-r['g'])}

def assembly(partition,tables,whole):
    block_witnesses=[join([tables[v] for v in block]) for block in partition]
    blocks=[[glue(w) for w in ws] for ws in block_witnesses]
    # These witnesses retain all local intermediate records, not only boundaries.
    hierarchical=[w for w in product(*block_witnesses)
                  if all(compatible(glue(x),glue(y)) for x in w for y in w)]
    images=[]
    for w in hierarchical:
        flat=glue([r for block in w for r in block])
        images.append(key(flat))
        inverse=tuple(tuple(proj(flat,schemas[v]) for v in block) for block in partition)
        require(inverse==w, 'split(flatten(w)) lost local witness')
        require(glue([r for b in inverse for r in b])==flat,'flatten(split)')
    require(set(images)==set(map(key,whole)),'assembly image not whole relation')
    require(len(images)==len(set(images)),'assembly target fibre not singleton')
    # Check independent block-level natural join too.
    require(set(key(glue(w)) for w in join(blocks))==set(images),'block cut differs')
    return hierarchical, [len(x) for x in block_witnesses]

def mission(whole):
    return [(g,t0,t1) for g in B for t0 in whole for t1 in whole
       if (t0['a'],t0['g'],t0['y'],t0['ok'])==(0,g,0,1)
       and (t1['a'],t1['g'],t1['y'],t1['ok'])==(1,g,1,1)]

summary=[]
for eP,eQ in product(B,repeat=2):
    tables=local_tables(eP,eQ)
    whole=rows(('a','g','n','p','y','ok'),lambda r:
        r['n']==1-r['g'] and r['p']==r['a']*(r['n']^eP)
        and r['y']==r['p']*(r['g']^eQ) and r['ok']==1-r['g'])
    require(len(whole)==4,'operational runs must remain nonempty')
    for a,g in product(B,repeat=2):
        require(len([r for r in whole if (r['a'],r['g'])==(a,g)])==1,'source fibre')
    hp,pc=assembly(physical,tables,whole)
    hf,fc=assembly(functional,tables,whole)
    for wp in hp:
        n,p,q,s=wp[0]+wp[1]
        wf=((n,s),(p,q))
        require(wf in hf,'label-preserving reindex absent')
        require(((wf[0][0],wf[1][0]),(wf[1][1],wf[0][1]))==wp,'reindex inverse')
        # Each square retains all component port records and internal wire values.
        require(glue([n,p,q,s])==glue([z for b in wf for z in b]),'root comparison square')
    goodP={g for g in B if all(a*((1-g)^eP)==a for a in B)}
    goodQ={g for g in B if all(d*(g^eQ)==d for d in B)}
    goodS={0}
    certificates=mission(whole)
    require({w[0] for w in certificates}==goodP & goodQ & goodS,'local vs mission exactness')
    require(len(certificates)==(1 if (eP,eQ)==(0,1) else 0),'wrong occurrence acceptance')
    summary.append({'adapter_P':eP,'adapter_Q':eQ,'operational_runs':len(whole),
      'physical_block_witnesses':pc,'functional_block_witnesses':fc,
      'mission_modes':sorted(w[0] for w in certificates),
      'signal_good_modes':sorted(goodP & goodQ)})

# Primitive component tables and typed graph-of-complement adapter.
board=rows(('d','c','z'),lambda r:r['z']==r['d']*r['c'])
require({tuple(r[x] for x in ('d','c','z')) for r in board}==
        {(0,0,0),(0,1,0),(1,0,0),(1,1,1)},'board truth table')
adapter={(g,1-g) for g in B}
require({(x,z) for x,y in adapter for yy,z in adapter if y==yy}=={(0,0),(1,1)},'adapter involution')
opened=rows(('p','g','j','y'),lambda r:r['j']==1-r['g'] and r['y']==r['p']*r['j'])
closed=rows(('p','g','y'),lambda r:r['y']==r['p']*(1-r['g']))
for c in closed:
    fibres=[r for r in opened if proj(r,('p','g','y'))==c]
    require(len(fibres)==1,'Qminus intermediate lift not singleton')
    require(fibres[0]['j']==1-c['g'],'wrong intermediate adapter witness')
require(len(opened)==len(closed)==4,'adapter table incomplete')

# Unaffected certificate/table reuse is literal equality, never global preservation.
t0,tq=local_tables(0,0),local_tables(0,1)
for v in ('N','P','S'):
    require(t0[v]==tq[v],'unaffected local table changed')
require(t0['Q']!=tq['Q'],'changed occurrence not distinguished')
require(physical[0]+physical[1]!=functional[0]+functional[1], 'crossed frontiers falsely planar')
# Typed-positionwise identification fails even if Boolean values happen to coincide.
require(schemas['P']!=schemas['S'],'permutation-free second coordinate falsely typed')

# Natural comparison after forgetting shared mode. These are GOOD certificate sets.
L={0};R={1};S={0}
fine=[(l,r,s) for l,r,s in product(L,R,S) if l==r==s]
coarse=[('*','*','*')]
require(len(fine)==0 and len(coarse)==1,'ghost lost')
require(not any(l==r==s for l,r,s in product(L,R,S)),'ghost falsely lifted')
# Exhaust all Boolean observation maps to Bool, including constants.
observation_results=[]
for q0,q1 in product(B,repeat=2):
    q={0:q0,1:q1}
    target=[(l,r,s) for l,r,s in product(L,R,S) if q[l]==q[r]==q[s]]
    reflects=(len(target)==len(fine))
    separates=q0!=q1
    require(reflects==separates,'mode repair exactness criterion')
    predicates=({0},{1})
    factors=all(all(q[x]!=q[y] or ((x in pred)==(y in pred)) for x,y in product(B,repeat=2)) for pred in predicates)
    require(factors==separates,'local-language minimality')
    observation_results.append({'q':[q0,q1],'ghost_count':len(target),'local_predicates_factor':factors})

# Literal sequential spans with carried wires, original and five-node repair.
span_results=[]
for repaired in (False,True):
    wn=('a','g','n','j','p','y','ok') if repaired else ('a','g','n','p','y','ok')
    w=rows(wn,lambda r:r['n']==1-r['g'] and r['ok']==1-r['g'] and
       r['p']==r['a']*r['n'] and
       (r['j']==1-r['g'] and r['y']==r['p']*r['j'] if repaired else r['y']==r['p']*r['g']))
    X=rows(('a','g','n','p'),lambda r:r['n']==1-r['g'] and r['p']==r['a']*r['n'])
    yn=('p','g','j','y','ok') if repaired else ('p','g','y','ok')
    Y=rows(yn,lambda r:r['ok']==1-r['g'] and
        (r['j']==1-r['g'] and r['y']==r['p']*r['j'] if repaired else r['y']==r['p']*r['g']))
    cn=('a','g','n','j','ok') if repaired else ('a','g','n','ok')
    C=rows(cn,lambda r:r['n']==r['ok']==1-r['g'] and (not repaired or r['j']==1-r['g']))
    dn=('a','n','j','g','ok','p','y') if repaired else ('a','n','g','ok','p','y')
    D=rows(dn,lambda r:r['p']==r['a']*r['n'] and r['y']==r['p']*(r['j'] if repaired else r['g']))
    for name,left,right in (('physical',X,Y),('functional',C,D)):
        witnesses=join((left,right))
        require(len(witnesses)==4,'sequential span witness count')
        require(set(key(glue(t)) for t in witnesses)==set(map(key,w)),'span image')
        for t in witnesses:
            r=glue(t)
            require((proj(r,tuple(left[0])),proj(r,tuple(right[0])))==t,'full span inverse')
        span_results.append({'repaired':repaired,'cut':name,'left':len(left),'right':len(right),'joint':len(witnesses)})
    if repaired:
        for r in w:
            # Nested physical cut X | (Qminus | S), then Qminus -> (J,Q).
            jrecord=proj(r,('g','j'))
            qrecord=proj(r,('p','j','y'))
            srecord=proj(r,('g','ok'))
            qm=glue((jrecord,qrecord))
            coarse_qm=proj(qm,('p','g','y'))
            lifts=[v for v in opened if proj(v,('p','g','y'))==coarse_qm]
            require(lifts==[qm],'nested module cut lost its exact internal lift')
            nested=(proj(r,('a','g','n','p')),(qm,srecord))
            require(glue((nested[0],glue(nested[1])))==r,'nested repaired full root')
        require(len(mission(w))==1,'five-node mission certificate')
    else:
        old_at_10=[r for r in w if (r['a'],r['g'])==(1,0)][0]
require((old_at_10['y'],old_at_10['ok'])==(0,1),'old endpoint')
new_at_10=[r for r in w if (r['a'],r['g'])==(1,0)][0]
require((new_at_10['y'],new_at_10['ok'])==(1,1),'new endpoint')
require(proj(old_at_10,('y','ok'))!=proj(new_at_10,('y','ok')),'invalid replacement root square accepted')

# Explicit same-whole G5 Theta at block level (independent of its definition).
box=join((X,Y)); fun=join((C,D))
for bx in box:
    whole_record=glue(bx)
    fx=(proj(whole_record,tuple(C[0])),proj(whole_record,tuple(D[0])))
    require(fx in fun,'G5 Theta not in functional pullback')
    require(glue(fx)==whole_record,'G5 Theta root square')
    back=(proj(glue(fx),tuple(X[0])),proj(glue(fx),tuple(Y[0])))
    require(back==bx,'G5 Theta inverse roundtrip')
for fx in fun:
    bx=(proj(glue(fx),tuple(X[0])),proj(glue(fx),tuple(Y[0])))
    require((proj(glue(bx),tuple(C[0])),proj(glue(bx),tuple(D[0])))==fx,'G5 reverse roundtrip')

# Actual contextual atomic spans from the manuscript. Enumerate every cut
# independently, including valuations not extendable to the whole mission.
def stage(ins,outs,equation):
    names=tuple(dict.fromkeys(ins+outs))
    return names,equation,rows(names,equation)
def stagepath(label,stages):
    for end in range(1,len(stages)+1):
        path=stages[:end]
        names=tuple(dict.fromkeys(n for ns,_,_ in path for n in ns))
        target=rows(names,lambda r:all(eq(r) for _,eq,_ in path))
        witnesses=join([table for _,_,table in path])
        require(len(witnesses)==len(target),label+' staged cardinality')
        require(set(key(glue(t)) for t in witnesses)==set(map(key,target)),label+' staged image')
        for t in witnesses:
            r=glue(t)
            require(tuple(proj(r,ns) for ns,_,_ in path)==t,label+' staged inverse')
    return len(stages[-1][2]),len(witnesses)
N=stage(('a','g'),('a','g','n'),lambda r:r['n']==1-r['g'])
P=stage(('a','g','n'),('p','g'),lambda r:r['p']==r['a']*r['n'])
Q=stage(('p','g'),('y','g'),lambda r:r['y']==r['p']*r['g'])
S=stage(('y','g'),('y','ok'),lambda r:r['ok']==1-r['g'])
stagepath('X',[N,P]);stagepath('Y',[Q,S]);stagepath('G physical',[N,P,Q,S])
Sf=stage(('a','g','n'),('a','n','g','ok'),lambda r:r['ok']==1-r['g'])
Pf=stage(('a','n','g','ok'),('p','g','ok'),lambda r:r['p']==r['a']*r['n'])
Qf=stage(('p','g','ok'),('y','ok'),lambda r:r['y']==r['p']*r['g'])
stagepath('Cbar',[N,Sf]);stagepath('Dbar',[Pf,Qf]);stagepath('G functional',[N,Sf,Pf,Qf])
J=stage(('p','g'),('p','g','j'),lambda r:r['j']==1-r['g'])
Qj=stage(('p','g','j'),('y','g'),lambda r:r['y']==r['p']*r['j'])
stagepath('Qminus',[J,Qj]);stagepath('Y5',[J,Qj,S]);stagepath('G5 physical',[N,P,J,Qj,S])
Jf=stage(('a','g','n'),('a','g','n','j'),lambda r:r['j']==1-r['g'])
S5=stage(('a','g','n','j'),('a','n','j','g','ok'),lambda r:r['ok']==1-r['g'])
P5=stage(('a','n','j','g','ok'),('p','j','g','ok'),lambda r:r['p']==r['a']*r['n'])
Q5=stage(('p','j','g','ok'),('y','ok'),lambda r:r['y']==r['p']*r['j'])
stagepath('C5',[N,Jf,S5]);stagepath('D5',[P5,Q5]);stagepath('G5 functional',[N,Jf,S5,P5,Q5])

print(json.dumps({'checker':'full labelled finite witnesses', 'checks':checks,
   'placements':summary,'sequential_spans':span_results,'forget_mode':{'fine_certificates':0,'coarse_certificates':1},
   'observations':observation_results,'crossing_is_planar_I4':False},indent=2,sort_keys=True))
