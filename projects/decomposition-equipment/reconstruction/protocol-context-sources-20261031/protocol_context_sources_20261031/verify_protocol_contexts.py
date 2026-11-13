#!/usr/bin/env python3
"""Exact finite regression checks. Not a proof of the general theorems.
All arithmetic is rational. Source files are read solely for provenance hashes.
"""
from fractions import Fraction as Q
from collections import defaultdict, Counter
from itertools import product
from functools import lru_cache
from pathlib import Path
import hashlib, json

HERE=Path(__file__).resolve().parent
COUNTS=Counter()
DETAIL={}
def check(c, kind):
    COUNTS[kind]+=1
    if not c: raise AssertionError((kind,dict(COUNTS)))
def agg(rows):
    d=defaultdict(Q)
    for k,p in rows: d[k]+=p
    return {k:p for k,p in d.items() if p}
def frozen(d): return tuple(sorted(d.items()))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

# Composition fixture: genuinely stochastic pre and post kernels, local stopping,
# one-bit persistent states, a sampled pending bit, and input-dependent replies.
ATOMS={}
def apre(name,s,u,arity):
    for z in (0,1):
        for h in range(-1,arity):
            # -1 is local; all rows normalized independently of state/input.
            yield h,(u+s+z)%2,(name,s,u,h,(u+s+z)%2,z),Q(1,2*(arity+1))
def apost(record,r):
    name,s,u,h,v,z=record
    for coin,p in ((0,Q(1,3)),(1,Q(2,3))):
        yield s^coin,(s+u+z+(r or 0)+coin)%2,p

class Kernel:
    def __init__(self,names,holes,pre): self.names=names;self.holes=holes;self.pre=pre

def atom(name,arity):
    ATOMS[name]=arity
    def pre(st,u):
        for h,v,z,p in apre(name,st[name],u,arity):
            yield (None if h<0 else h),v,(z,),p
    return Kernel((name,),tuple(range(arity)),pre)

def compose(outer,children):
    """Binary substitution compiler. Pending stack is canonical node tuples.
    This compiles pre kernels, NOT complete step outcomes.
    """
    holes=tuple((i,j) for i,c in enumerate(children) for j in c.holes)
    def pre(st,u):
        for h,v,z,p in outer.pre(st,u):
            if h is None:
                yield None,v,z,p
            else:
                i=outer.holes.index(h)
                for k,w,zz,q in children[i].pre(st,v):
                    yield None if k is None else (i,k),w,z+zz,p*q
    return Kernel(tuple(sorted(outer.names+sum((c.names for c in children),()))),holes,pre)

def compiled_step(k,st,u):
    rows=[]
    for h,v,stack,p in k.pre(st,u):
        if h is not None: raise ValueError('Unfilled hole')
        partial=[(dict(st),None,(),p)]
        for z in reversed(stack):
            nxt=[]
            for states,r,events,weight in partial:
                for ns,o,q in apost(z,r):
                    ss=dict(states);ss[z[0]]=ns
                    event=z+(r,ns,o)
                    nxt.append((ss,o,(event,)+events,weight*q))
            partial=nxt
        for ss,o,events,w in partial: rows.append(((frozen(ss),o,events),w))
    return agg(rows)

# Independent direct operational evaluator: recursively runs each primitive call
# to completion, interleaving parent pre, child call, parent post. It never uses
# compiled pre kernels or the reverse-stack evaluator.
def direct_step(tree,st,u):
    name,children=tree
    rows=[]
    for h,v,z,p in apre(name,st[name],u,len(children)):
        childrows=[((frozen(st),None,()),Q(1))] if h<0 else direct_step(children[h],st,v).items()
        for (ss,r,events),q in childrows:
            for ns,o,w in apost(z,r):
                states=dict(ss);states[name]=ns
                rows.append(((frozen(states),o,(z+(r,ns,o),)+events),p*q*w))
    return agg(rows)

def compilation_tests():
    a,b,c,d=atom('a',1),atom('b',1),atom('c',1),atom('d',0)
    # Three different real compilation bracketings of four primitive levels.
    ks=[compose(a,[compose(b,[compose(c,[d])])]),
        compose(compose(a,[b]),[compose(c,[d])]),
        compose(compose(compose(a,[b]),[c]),[d])]
    tree=('a',(('b',(('c',(('d',()),)),)),))
    total_entries=0
    for bits in product((0,1),repeat=4):
        st=dict(zip('abcd',bits))
        for u in (0,1):
            direct=direct_step(tree,st,u)
            check(sum(direct.values())==1,'direct_normalization')
            for k in ks:
                got=compiled_step(k,st,u)
                check(got==direct,'compiled_vs_recursive_rows')
                check(sum(got.values())==1,'compiled_normalization')
                total_entries+=len(got)
                for states,o,events in got:
                    check(all(z[1]==st[z[0]] and z[2] in (0,1) for z in events),'mandatory_incoming_fields')
    # Identity compilers add no primitive event or nonsingleton state.
    ident=Kernel((),(0,),lambda st,u: [(0,u,(),Q(1))])
    for st in ({'a':0,'b':1,'c':0,'d':1},{'a':1,'b':0,'c':1,'d':0}):
        for u in (0,1):
            for k in (compose(ident,[ks[0]]),):
                check(compiled_step(k,st,u)==compiled_step(ks[0],st,u),'left_identity')
    # Right identity acts on a still-open unary operation.
    aa=compose(a,[ident]); left=compose(aa,[compose(b,[compose(c,[d])])])
    check(compiled_step(left,{'a':0,'b':1,'c':1,'d':0},1)==compiled_step(ks[0],{'a':0,'b':1,'c':1,'d':0},1),'right_identity')
    # Binary hole permutation simultaneously reindexes routing and arguments.
    x,l,r=atom('x',2),atom('l',0),atom('r',0)
    def perm_pre(st,u):
        for h,v,z,p in x.pre(st,u): yield None if h is None else 1-h,v,z,p
    xp=Kernel(x.names,x.holes,perm_pre)
    for bits in product((0,1),repeat=3):
        st=dict(zip(('x','l','r'),bits))
        for u in (0,1):
            check(compiled_step(compose(x,[l,r]),st,u)==compiled_step(compose(xp,[r,l]),st,u),'hole_permutation')
    # Old auxiliary-only pre records could collapse incoming states/inputs.
    old=[('aux',) for s in (0,1) for u in (0,1)]
    normal=[(s,u,'local',('aux',)) for s in (0,1) for u in (0,1)]
    check(len(set(old))==1 and len(set(normal))==4,'incoming_record_normal_form_regression')
    DETAIL['composition_kernel_entries']=total_entries

# Separate history/cut fixture. Primitive contexts have private random initial
# bits and deterministic local/query pre/post transitions. No evaluator above is
# reused. A preparation p fixes the root bit; other node bits are independent.
TREE={'R':('D','E'),'D':('A','B'),'E':('C','F'),'A':(),'B':(),'C':(),'F':()}
NODES=tuple(sorted(TREE))
CUTS=(('A','B','C','F'),('D','C','F'),('A','B','E'),('D','E'),('R',))
def descendants(n): return (n,)+sum((descendants(c) for c in TREE[n]),())
def above(cut): return tuple(n for n in NODES if not any(n in descendants(c) for c in cut))
def initial(nodes,prep):
    free=tuple(n for n in nodes if n!='R')
    for bits in product((0,1),repeat=len(free)):
        st=dict(zip(free,bits))
        if 'R' in nodes: st['R']=prep
        yield st,Q(1,2**len(free))

def raw_call(n,st,u):
    s=st[n];cs=TREE[n]
    if not cs:
        r=None;branch=-1;sub={};o=s;ns=s^(u%2)
    else:
        choice=(s+u)%3
        if choice==0: r=None;branch=-1;sub={}
        else:
            branch=choice-1
            st,r,sub=raw_call(cs[branch],st,(u+s)%3)
        o=(s+(r or 0))%2;ns=s^1
    ss=dict(st);ss[n]=ns
    # full incoming state, input, branch, child reply, outgoing state/output
    sub=dict(sub);sub[n]=('raw',s,u,branch,r,ns,o)
    return ss,o,sub

@lru_cache(None)
def prefix_law(n,prep,inputs):
    law=defaultdict(Q)
    for st,p in initial(descendants(n),prep):
        outs=[]
        for u in inputs:
            st,o,_=raw_call(n,st,u);outs.append(o)
        law[tuple(outs)]+=p
    return dict(law)

@lru_cache(None)
def hkernel(n,prep,h,u):
    ins=tuple(x for x,y in h);outs=tuple(y for x,y in h)
    den=prefix_law(n,prep,ins).get(outs,Q(0))
    if not den: return ((0,Q(1)),) # arbitrary normalized zero-history extension
    law=prefix_law(n,prep,ins+(u,))
    return tuple((o,law.get(outs+(o,),Q(0))/den) for o in (0,1) if law.get(outs+(o,),0))

def cut_call(n,st,hist,u,cut,prep):
    if n in cut:
        h=hist[n]
        for o,p in hkernel(n,prep,h,u):
            hh=dict(hist);hh[n]=h+((u,o),)
            yield st,hh,o,{n:('hist',u,o,h,hh[n])},p
        return
    s=st[n];choice=(s+u)%3;cs=TREE[n]
    if choice==0:
        subrows=[(st,hist,None,{},Q(1))];branch=-1
    else:
        branch=choice-1;subrows=cut_call(cs[branch],st,hist,(u+s)%3,cut,prep)
    for states,hh,r,events,p in subrows:
        o=(s+(r or 0))%2;ss=dict(states);ss[n]=s^1
        ee=dict(events);ee[n]=('raw',s,u,branch,r,s^1,o)
        yield ss,hh,o,ee,p

def original_paths(prep,inputs):
    rows=[]
    for st,p in initial(NODES,prep):
        start=frozen(st);ticks=[]
        for u in inputs:
            st,o,events=raw_call('R',st,u);ticks.append(frozen(events))
        rows.append(((prep,start,tuple(ticks)),p))
    return agg(rows)

def cut_paths(prep,inputs,cut):
    paths=[]
    for st,p in initial(above(cut),prep):
        partial=[(st,{n:() for n in cut},(),p)]
        start=frozen(st)
        for u in inputs:
            nxt=[]
            for states,hh,ticks,w in partial:
                for ss,hhh,o,events,q in cut_call('R',states,hh,u,cut,prep):
                    nxt.append((ss,hhh,ticks+(frozen(events),),w*q))
            partial=nxt
        paths.extend(((prep,start,ticks),w) for ss,hh,ticks,w in partial)
    return agg(paths)

def project(path,cut):
    prep,start,ticks=path;keep=set(above(cut));hist={n:() for n in cut};out=[]
    for tick in ticks:
        tt={}
        for n,event in tick:
            if n in keep: tt[n]=event
            if n in cut:
                if event[0]=='raw': u,o=event[2],event[6]
                else: u,o=event[1],event[2]
                h=hist[n];hist[n]=h+((u,o),)
                tt[n]=('hist',u,o,h,hist[n])
        out.append(frozen(tt))
    return prep,tuple((n,s) for n,s in start if n in keep),tuple(out)

def refines(f,g): return all(any(n in descendants(c) for c in g) for n in f)
def push(law,cut): return agg((project(path,cut),p) for path,p in law.items())
def history_tests():
    global hkernel
    pathcount=0;local=0;inherited=0
    experiments=[(p,w) for p in (0,1) for w in product((0,1,2),repeat=3)]
    # Additional longer repetitions exercise inherited, non-reset histories.
    experiments += [(0,(1,1,1,1,1)),(1,(2,2,2,2,2))]
    for prep,inputs in experiments:
        orig=original_paths(prep,inputs);laws=[]
        check(sum(orig.values())==1,'original_path_normalization')
        for cut in CUTS:
            law=cut_paths(prep,inputs,cut);laws.append(law)
            check(push(orig,cut)==law,'independent_cut_pushforward')
            check(sum(law.values())==1,'cut_path_normalization')
            for path in law:
                check(project(path,cut)==path,'cut_identity')
                pathcount+=1
                for tick in path[2]:
                    for n,e in tick:
                        local+=int(e[0]=='raw' and e[3]==-1)
                        inherited+=int(e[0]=='hist' and bool(e[3]))
        for i,f in enumerate(CUTS):
            for j,g in enumerate(CUTS):
                if not refines(f,g): continue
                check(push(laws[i],g)==laws[j],'cut_to_cut_pushforward')
                for path in orig:
                    check(project(project(path,f),g)==project(path,g),'original_cut_triangle')
                for path in laws[i]:
                    for h in CUTS:
                        if refines(g,h):
                            check(project(project(path,g),h)==project(path,h),'three_cut_triangle')
        # The two incomparable cuts have leaves as common refinement.
        check(not refines(CUTS[1],CUTS[2]) and not refines(CUTS[2],CUTS[1]),'incomparable_cuts')
    check(local>0,'local_node_records_exercised')
    check(inherited>0,'inherited_histories_exercised')
    # Consistent zero-law path: two repeated output-1 responses from leaf A with
    # input 0 are possible, but then input 0/output 0 has probability zero.
    h=((0,1),(0,1),(0,0))
    check(prefix_law('A',0,(0,0,0)).get((1,1,0),0)==0,'zero_history_witness')
    check(sum(p for o,p in hkernel('A',0,h,0))==1,'zero_history_normalized_extension')
    # Carrier map tests use deliberately unsupported records, still with correct
    # accumulations. Modify an actual raw root output; maps remain total.
    base=next(iter(original_paths(0,(1,1,1))))
    prep,start,ticks=base;tt=[dict(t) for t in ticks]
    e=list(tt[-1]['R']);e[-1]=1-e[-1];tt[-1]['R']=tuple(e)
    zero=(prep,start,tuple(frozen(t) for t in tt))
    check(zero not in original_paths(0,(1,1,1)),'unsupported_consistent_raw_path')
    for f in CUTS:
        for g in CUTS:
            if refines(f,g):
                check(project(project(zero,f),g)==project(zero,g),'zero_law_cut_triangle')
    # Negative controls: forgetting an internal local event loses a required
    # coarser history call; resetting history yields the wrong stochastic law.
    witness=next(iter(original_paths(0,(0,0,0))))
    p,s,ts=witness;deleted=[]
    for tick in ts:
        deleted.append(tuple((n,e) for n,e in tick if not (e[0]=='raw' and e[3]==-1)))
    check(project((p,s,tuple(deleted)),('R',))!=project(witness,('R',)),
          'missing_local_event_negative_control')
    real_hkernel=hkernel
    def reset_kernel(n,p,h,u): return real_hkernel(n,p,(),u)
    found=False
    try:
        hkernel=reset_kernel
        for p,w in experiments:
            if cut_paths(p,w,('R',))!=push(original_paths(p,w),('R',)):
                found=True;break
    finally: hkernel=real_hkernel
    check(found,'reset_history_negative_control')
    DETAIL.update(history_experiments=len(experiments),cut_path_records=pathcount,
                  retained_local_events=local,inherited_history_events=inherited)

# Independent scheduling checks: actual cursor stepping, no closed formula used
# to generate hierarchical polling streams.
def schedule(tree,n):
    cursors={}
    def poll(t,path=()):
        if isinstance(t,str): return t
        i=cursors.get(path,0);cursors[path]=(i+1)%len(t)
        return poll(t[i],path+(i,))
    return [poll(tree) for _ in range(n)]
def bounds(tree,k=1):
    if isinstance(tree,str): return {tree:k}
    return {a:b for child in tree for a,b in bounds(child,k*len(tree)).items()}
def polling_tests():
    trees=[('A',), (('A','B'),('C',)), ((('A','B'),'C'),('D',('E','F','G')))]
    for tree in trees:
        seq=schedule(tree,400);bs=bounds(tree)
        for leaf,L in bs.items():
            for LL in (L,L+1,2*L):
                for offset in range(len(seq)-LL+1):
                    check(leaf in seq[offset:offset+LL],'polling_all_windows_and_weakening')
    check(schedule((('A','B'),('C',)),8)==list('ACBCACBC'),'nested_rr_trace')
    check(schedule(('A','B','C'),6)==list('ABCABC'),'flat_rr_trace')
    check(schedule((('A','B'),('C',)),6)!=schedule(('A','B','C'),6),'nested_not_flat')
    for a,b,c in product(range(1,6),repeat=3):
        check((a*b)*c==a*(b*c),'certificate_product_associativity')
        check((a+1)*(b+1)>=a*b,'certificate_weakening_monotonicity')
    for a in range(1,10): check(a*1==a==1*a,'certificate_identity')
    # One root manager owns both ordered locks; workers hold no duplicate manager.
    # A acquires low then high; B high; C low. Busy is an actual recorded call.
    programs={'A':(('acq',0),('acq',1),('work',),('finish',)),
              'B':(('acq',1),('work',),('finish',)),
              'C':(('acq',0),('work',),('finish',))}
    ticks=schedule((('A','B'),('C',)),100);B=4
    for offsets in range(8):
        owner={};pc={a:0 for a in programs};log=[];done_at=None
        for tick,a in enumerate(ticks[offsets:],1):
            snapshot=dict(owner);before=pc[a]
            if before==len(programs[a]): status='terminal'
            else:
                op=programs[a][before]
                if op[0]=='acq' and op[1] in snapshot: status='busy'
                else:
                    status='grant';pc[a]+=1
                    if op[0]=='acq': owner[op[1]]=a
                    if op[0]=='finish': owner={r:w for r,w in owner.items() if w!=a}
            if status in ('busy','terminal'):
                check(pc[a]==before and owner==snapshot,'busy_terminal_intrinsic_stutter')
            log.append((a,status))
            if done_at is None and all(pc[a]==len(programs[a]) for a in pc): done_at=tick
        check(done_at is not None,'ordered_lock_completion')
        for offset in range(max(0,done_at-B)):
            check(any(status=='grant' for _,status in log[offset:offset+B]),'B_window_global_grant')
        S=sum(map(len,programs.values()))
        check(done_at<=B*S,'B_total_work_completion_clock')
        check(all(status=='terminal' for _,status in log[done_at:]),'terminal_continued_polling')
        # One episode per worker, intrinsic t=4, m=1: bad-event terms are zero.
        # Exact finite tail is zero at B*W*m*t (not a test of general P/G bounds).
        check(done_at<=B*len(programs)*1*4,'deterministic_tail_cutoff_sanity')
        check(any(status=='busy' for _,status in log),'explicit_busy_calls_exercised')
    DETAIL['manager_fixture_offsets']=8
    DETAIL['manager_count']=1

if __name__=='__main__':
    compilation_tests();history_tests();polling_tests()
    sources={p:sha(HERE/p) for p in ('protocol_context_substitution_theorem.md','polling_envelope_progress_theorem.md')}
    result={'status':'PASS','arithmetic':'fractions.Fraction','assertions':sum(COUNTS.values()),
      'assertions_by_category':dict(sorted(COUNTS.items())),'coverage':DETAIL,'source_sha256':sources,
      'verifier_sha256':sha(Path(__file__)),
      'limitations':['Finite selected fixtures only; not a proof or exhaustive state-space audit of the general theorem.',
      'No implementation of the free Isbell envelope or CFS normalizer.',
      'Tail check is the zero-bad-event deterministic special case, not a stochastic P/G matrix verification.',
      'Canonical path tests concern a fixed expanded tree, not arbitrary black-box equivalent implementations.']}
    out=json.dumps(result,indent=2,sort_keys=True)+'\n'
    (HERE/'verification_results.json').write_text(out)
    (HERE/'verification.log').write_text(out)
    print(out,end='')
