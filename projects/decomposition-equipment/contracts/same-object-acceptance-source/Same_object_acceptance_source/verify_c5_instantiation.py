#!/usr/bin/env python3
"""Finite independent C5 instance checks, not a kernel proof of C5.
Original graphs are ordered/simple/undirected. Full typed arrow strings and
occurrence embeddings are retained; equal composite values do not identify cuts.
"""
from dataclasses import dataclass,replace
from itertools import product
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

N=0

def ck(test,message):
    global N
    if not test: raise AssertionError(message)
    N+=1

def bits(n): return tuple(product((0,1),repeat=n))
def xor(x):
    a=0
    for b in x:a^=b
    return a

@dataclass(frozen=True)
class Obj:
    tag:str
    dim:int
    @property
    def values(self):return bits(self.dim)

@dataclass(frozen=True)
class Arrow:
    source:Obj
    target:Obj
    table:tuple
    def __call__(self,x):return self.table[self.source.values.index(x)]


def arrow(a,b,fn):
    table=tuple(fn(x) for x in a.values)
    ck(all(y in b.values for y in table),'arrow totality and codomain')
    return Arrow(a,b,table)

def identity(a):return Arrow(a,a,a.values)

def compose(fs):
    ck(bool(fs),'nonempty path required by compose')
    for a,b in zip(fs,fs[1:]):ck(a.target==b.source,'actual intermediate carrier matches')
    def fn(x):
        for f in fs:x=f(x)
        return x
    return arrow(fs[0].source,fs[-1].target,fn)

@dataclass(frozen=True)
class Graph:
    size:int
    edges:frozenset
    def restrict(self,U):
        U=tuple(sorted(U));position={v:i for i,v in enumerate(U)}
        return Graph(len(U),frozenset((position[a],position[b]) for a,b in self.edges if a in position and b in position))


def pathgraph(s):
    # Chronological dependency shadow with selected side-wire dependencies.
    return Graph(s,frozenset([(i,i+1) for i in range(s-1)]+[(i,i+2) for i in range(s-2)]))

@dataclass(frozen=True)
class Flat:
    graph:Graph
    blocks:tuple
    arrows:tuple
    output:Arrow
    scalar:int=1
    def validate(self):
        ck(all(0<=a<b<self.graph.size for a,b in self.graph.edges),'ordered simple undirected whole graph')
        ck(all(U==tuple(sorted(U)) for U in self.blocks),'blocks use canonical increasing enumeration')
        ck(len(self.blocks)==len(self.arrows),'full profile length')
        vertices=[v for U in self.blocks for v in U]
        ck(sorted(vertices)==list(range(self.graph.size)),'actual disjoint cover')
        ck(self.scalar==1,'probability not illicit C5 scalar')
        if self.arrows:ck(compose(self.arrows)==self.output,'output actual composite')
        else:ck(self.graph.size==0 and self.output==identity(self.output.source),'U only empty identity output')
        return self

@dataclass(frozen=True)
class Leaf:
    graph:Graph
    value:Arrow

@dataclass(frozen=True)
class Unit:
    obj:Obj

@dataclass(frozen=True)
class Cut:
    graph:Graph
    left_vertices:tuple
    right_vertices:tuple
    left:object
    right:object

@dataclass(frozen=True)
class Decor:
    value:int
    child:object


def evalterm(t):
    if isinstance(t,Leaf):return Flat(t.graph,(tuple(range(t.graph.size)),),(t.value,),t.value).validate()
    if isinstance(t,Unit):return Flat(Graph(0,frozenset()),(),(),identity(t.obj)).validate()
    if isinstance(t,Decor):
        ck(t.value==1,'only original unit scalar here'); return evalterm(t.child)
    ck(t.left_vertices==tuple(sorted(t.left_vertices)) and t.right_vertices==tuple(sorted(t.right_vertices)),
       'binary embeddings use canonical increasing order')
    l,r=evalterm(t.left),evalterm(t.right)
    ck(l.graph==t.graph.restrict(t.left_vertices),'left actual induced graph')
    ck(r.graph==t.graph.restrict(t.right_vertices),'right actual induced graph')
    ck(sorted(t.left_vertices+t.right_vertices)==list(range(t.graph.size)),'binary ordered partition')
    blocks=tuple(tuple(U[j] for j in V) for U,f in ((t.left_vertices,l),(t.right_vertices,r)) for V in f.blocks)
    return Flat(t.graph,blocks,l.arrows+r.arrows,compose((l.output,r.output))).validate()


def local_flat(flat,indices):
    indices=tuple(indices)
    U=tuple(sorted(v for i in indices for v in flat.blocks[i])); pos={v:j for j,v in enumerate(U)}
    fs=tuple(flat.arrows[i] for i in indices)
    return U,Flat(flat.graph.restrict(U),tuple(tuple(pos[v] for v in flat.blocks[i]) for i in indices),fs,compose(fs)).validate()


def comb(flat,right=True):
    if not flat.arrows:return Unit(flat.output.source)
    if len(flat.arrows)==1:return Leaf(flat.graph,flat.arrows[0])
    pivot=1 if right else len(flat.arrows)-1
    U,l=local_flat(flat,range(pivot));V,r=local_flat(flat,range(pivot,len(flat.arrows)))
    return Cut(flat.graph,U,V,comb(l,right),comb(r,right))



def rotate_R(t):
    """Original labelled R, using actual subset unions and increasing maps."""
    ck(isinstance(t,Cut) and isinstance(t.left,Cut),'R actual typed redex')
    inner=t.left
    X=tuple(t.left_vertices[j] for j in inner.left_vertices)
    Y=tuple(t.left_vertices[j] for j in inner.right_vertices)
    Z=t.right_vertices
    YZ=tuple(sorted(Y+Z)); positions={v:i for i,v in enumerate(YZ)}
    right=Cut(t.graph.restrict(YZ),tuple(positions[v] for v in Y),tuple(positions[v] for v in Z),inner.right,t.right)
    result=Cut(t.graph,X,YZ,inner.left,right)
    ck(evalterm(t)==evalterm(result),'R preserves whole graph/full typed path/embeddings')
    return result


def normalize_R(t):
    if not isinstance(t,Cut):return t
    while isinstance(t.left,Cut): t=rotate_R(t)
    return replace(t,right=normalize_R(t.right))

def singleton(fs):
    return Flat(pathgraph(len(fs)),tuple((i,) for i in range(len(fs))),tuple(fs),compose(fs)).validate()


def substitute(outer,inners):
    ck(len(inners)==len(outer.blocks),'occurrence-indexed substitution arity')
    blocks=[];arrows=[]
    for U,f,g in zip(outer.blocks,outer.arrows,inners):
        ck(g.graph==outer.graph.restrict(U),'substitution original graph restriction')
        ck(g.output==f,'substitution actual arrow factorization')
        for V in g.blocks:blocks.append(tuple(U[j] for j in V))
        arrows.extend(g.arrows)
    return Flat(outer.graph,tuple(blocks),tuple(arrows),outer.output).validate()


def coarse_of(fine,groups):
    inners=[];blocks=[];fs=[]
    for group in groups:
        U,part=local_flat(fine,group)
        blocks.append(U);fs.append(part.output);inners.append(part)
    outer=Flat(fine.graph,tuple(blocks),tuple(fs),fine.output).validate()
    return outer,tuple(inners)


def physical_path(chart,tiles):
    # Each tile retains all later actual inputs as side wires. Full stage tags
    # preserve distinct intermediate carriers, even for identity-valued sends.
    dim=1+2*tiles; current=Obj(f'{chart}:input',dim); fs=[]; licenses=[]
    for tile in range(tiles):
        actions=('xor1','send-b','xor2') if chart=='C' else ('send-uv','xor1','xor2')
        for action in actions:
            outdim=dim-1 if action.startswith('xor') else dim
            target=Obj(f'{chart}:tile{tile}:{action}',outdim)
            fn=(lambda x:(x[0]^x[1],)+x[2:]) if action.startswith('xor') else (lambda x:x)
            fs.append(arrow(current,target,fn));licenses.append((f'physical:{chart}:{tile}:{action}',action))
            current=target;dim=outdim
        if tile+1<tiles:
            target=Obj(f'{chart}:seam{tile}',dim)
            fs.append(arrow(current,target,lambda x:x));licenses.append((f'physical:{chart}:seam{tile}','send-seam'))
            current=target
    return singleton(fs),tuple(licenses)


def licensed(path,records,available):
    return len(path.arrows)==len(records) and all(event in available for event,action in records if action.startswith('send'))


def verify_terms():
    summaries=[]
    for chart in ('C','R'):
      for tiles in (1,2):
        flat,licenses=physical_path(chart,tiles)
        right,left=comb(flat,True),comb(flat,False)
        ck(evalterm(right)==flat and evalterm(left)==flat,'typed left/right comb evaluation equality')
        ck(comb(evalterm(left),True)==right,'actual flat normalization preserves full profile')
        ck(normalize_R(left)==right,'labelled R steps reach exact original rightcomb')
        for x in flat.output.source.values:ck(flat.output(x)==(xor(x),),'actual physical composite')
        external=Obj(f'physical:early:{1+2*tiles}',1+2*tiles)
        actuator=Obj('physical:actuator-bit',1)
        initialize=arrow(external,flat.output.source,lambda x:x)
        readout=arrow(flat.output.target,actuator,lambda x:x)
        external_function=compose((initialize,flat.output,readout))
        for x in external.values:ck(external_function(x)==(xor(x),),'typed rho Phi iota physical boundary map')
        allowed={e for e,a in licenses if a.startswith('send')}
        ck(licensed(flat,licenses,allowed),'original message permissions')
        erased=set(allowed);erased.remove(next(iter(allowed)))
        ck(not licensed(flat,licenses,erased),'value equality cannot erase message license')
        # True UL/UR unit cases have no external occurrence, unlike message leaf.
        U=Unit(flat.output.source)
        unit_left=Cut(flat.graph,(),tuple(range(flat.graph.size)),U,right)
        ck(evalterm(unit_left)==flat,'typed UL actual nullary')
        U2=Unit(flat.output.target)
        unit_right=Cut(flat.graph,tuple(range(flat.graph.size)),(),right,U2)
        ck(evalterm(unit_right)==flat,'typed UR actual nullary')
        ck(evalterm(Decor(1,right))==flat,'D0 unit scalar only')
        message_index=1 if chart=='C' else 0
        f=flat.arrows[message_index]
        ck(f.table==f.source.values and f.source!=f.target,'identity values still updated stage tag')
        msg=evalterm(Leaf(flat.graph.restrict((message_index,)),f))
        ck(msg.graph.size==1 and len(msg.arrows)==1,'message is a nonempty external occurrence')
        ck(msg!=evalterm(Unit(f.source)),'nonempty message not nullary U')
        empty_leaf=evalterm(Leaf(Graph(0,frozenset()),identity(f.source)))
        ck(empty_leaf!=evalterm(Unit(f.source)) and len(empty_leaf.arrows)==1,
           'even empty-colour identity leaf is external occurrence not U')
        bad=list(flat.arrows); middle=bad[1]
        bad[1]=replace(middle,source=Obj('wrong-intermediate-tag',middle.source.dim))
        try: compose(tuple(bad))
        except AssertionError: rejected=True
        else: rejected=False
        ck(rejected,'equal-looking table with wrong typed boundary rejected')
        if tiles==2:
            # Coarse (tile1,seam,tile2) and actual occurrence refinements.
            outer,inners=coarse_of(flat,(range(3),range(3,4),range(4,7)))
            ck(substitute(outer,inners)==flat,'actual tile-to-stages substitution')
            nonincreasing=replace(outer,blocks=(tuple(reversed(outer.blocks[0])),)+outer.blocks[1:])
            try: nonincreasing.validate()
            except AssertionError: rejected=True
            else: rejected=False
            ck(rejected,'nonincreasing occurrence embedding rejected')
            # Partial then nested refinement vs simultaneous substitution.
            first=Flat(flat.graph,tuple((i,) for i in range(3))+(outer.blocks[1],outer.blocks[2]),
                       flat.arrows[:3]+outer.arrows[1:],flat.output).validate()
            trivial=tuple(Flat(first.graph.restrict(U),(tuple(range(len(U))),),(f,),f).validate()
                          for U,f in zip(first.blocks[:-1],first.arrows[:-1]))
            ck(substitute(first,trivial+(inners[2],))==flat,'nested occurrence substitution coherence')
            # Actual labelled R rotation on the 3 coarse blocks.
            ck(evalterm(comb(outer,False))==evalterm(comb(outer,True)),'R uses actual unions/full arrows')
            for U,g in zip(outer.blocks,inners):
                for V in g.blocks:
                    lifted=tuple(U[j] for j in V)
                    ck(g.graph.restrict(V)==outer.graph.restrict(lifted),'strict iterated restriction graph')
                    ck(tuple(U[j] for j in V)==tuple(sorted(lifted)),'increasing embeddings compose literally')
            # Whole graph survives even if all singleton induced pieces agree.
            mutated=replace(flat,graph=Graph(flat.graph.size,frozenset()))
            ck(mutated!=flat,'same singleton pieces do not identify whole graph')
        summaries.append({'chart':chart,'tiles':tiles,'stages':len(flat.arrows),'inputs':len(flat.output.source.values),
                          'intermediate_dimensions':[flat.arrows[0].source.dim]+[f.target.dim for f in flat.arrows]})
    c,_=physical_path('C',1);r,_=physical_path('R',1)
    ck(tuple(c.output(x) for x in bits(3))==tuple(r.output(x) for x in bits(3)),'cross-chart external value equality')
    ck(c.arrows!=r.arrows,'crossing charts not same full arrow profile')
    return summaries


def representative(a,u,v,redraw=None):
    source={'rep:u':u,'rep:v':v};held={};events=[];outputs=[];parity=a
    # Expose consumes named event once. The common fine record retains emissions.
    held['s']=source['rep:u'];held['sid']='rep:u';outputs.append(('z1',u));events.append(('expose','rep:u',u))
    delivered=held['s'] if redraw is None else redraw
    delivered_id=held['sid'] if redraw is None else 'rep:u:illegal-redraw'
    held['t']=delivered;events.append(('deliver',delivered_id,delivered))
    b=parity^held['t'];outputs.append(('r1',b));events.append(('xor1','rep:u',b))
    held['s']=source['rep:v'];held['sid']='rep:v';outputs.append(('z2',v));events.append(('expose','rep:v',v))
    held['t']=held['s'];events.append(('deliver',held['sid'],held['t']))
    c=b^held['t'];outputs.append(('r2',c));events.append(('xor2','rep:v',c))
    events.append(('seam',c))
    return tuple(outputs),tuple(events),c


def verify_representative():
    probabilities=Counter();mutation_mismatch=0
    for a,u,v in bits(3):
        out,events,c=representative(a,u,v)
        ck(tuple(x[1] for x in out)==(u,a^u,v,a^u^v),'seven-stage representative output')
        ck(len(events)==7,'actual representative event schedule')
        ck(events[0][1:]==events[1][1:] and events[3][1:]==events[4][1:],'persistent source delivery identity')
        probabilities[(a,u,v,c)]+=F(1,8)
        for fresh in (0,1):
            bad,be,bc=representative(a,u,v,redraw=fresh)
            ck(be[0][1]!=be[1][1],'redraw violates named event witness regardless of coincident value')
            mutation_mismatch+=bad[1][1]!=(a^u)
    ck(sum(probabilities.values())==1 and all(p>0 for p in probabilities.values()),'external positive preparation')
    qlaw=Counter()
    for (a,u,v,c),weight in probabilities.items():
        ck((a^u^v,c)==(c,c),'representative q_d g_d equals parity diagonal pi')
        qlaw[(a^u^v,c)]+=weight
    ck(qlaw=={(0,0):F(1,2),(1,1):F(1,2)},'actual representative preparation pushes to uniform O')
    ck(mutation_mismatch==8,'independent redraw changes shared source law with probability one half')
    # Conditional physical circuit tables, including source coordinate side wires,
    # evaluated as actual typed maps; source preparation is not a C5 scalar.
    carrier=Obj('rep:initial',8) # a,u,v,s,t,b,c,phase-valid
    valid_inputs=[(a,u,v,0,0,0,0,1) for a,u,v in bits(3)]
    fs=[];cur=carrier
    for step in range(7):
        target=Obj(f'rep:step{step+1}',8)
        def fn(x,step=step):
            a,u,v,s,t,b,c,ok=x
            if not ok:return (0,)*8 # absorbing malformed sentinel
            if step==0:s=u
            elif step==1:t=s
            elif step==2:b=a^t
            elif step==3:s=v
            elif step==4:t=s
            elif step==5:c=b^t
            return a,u,v,s,t,b,c,ok
        fs.append(arrow(cur,target,fn));cur=target
    flat=singleton(fs)
    ck(evalterm(comb(flat))==flat,'representative genuine typed rightcomb')
    for x in valid_inputs:ck(flat.output(x)[6]==xor(x[:3]),'conditional representative arrow composite')
    external=Obj('representative:external-source',3)
    captured=Obj('representative:captured-record',5)
    observable=Obj('mission:O',2)
    initialize=arrow(external,carrier,lambda x:x+(0,0,0,0,1))
    readout=arrow(flat.output.target,captured,lambda x:(x[0],x[1],x[5],x[2],x[6]))
    g=compose((initialize,flat.output,readout))
    q=arrow(captured,observable,lambda w:(w[0]^w[1]^w[3],w[4]))
    qg=compose((g,q))
    for x in external.values:ck(qg(x)==(xor(x),xor(x)),'typed representative q rho Phi iota boundary square')
    for f in fs:ck(f((0,)*8)==(0,)*8,'failure sentinel absorbing')
    return {'valid_inputs':8,'seven_stage_arrow_domain_size':256,'redraw_mismatch_fraction':'1/2',
            'scope':'finite admitted initialization; external operational phase/license witnesses retained'}


def uniform(values):
    counts=Counter(values);return {v:F(c,counts.total()) for v,c in counts.items()}


def verify_same_joint_w():
    c,_=physical_path('C',2);r,_=physical_path('R',2)
    good=[];correlated=[]
    for x in bits(5):
        d=xor(x);good.append((x,d))
        if x[1]==x[2]:correlated.append((x,d))
    target={(0,0):F(1,2),(1,1):F(1,2)}
    for support in (good,correlated):
        for term in (c,r):
            hd=[(term.output(x)[0],d) for x,d in support]
            ck(uniform(hd)==target,'h_d pushes actual joint physical support to diagonal O')
            for (x,d),h in zip(support,hd):
                ck(h==(xor(x),d),'same-w h_d equals q_T pointwise')
                for y in bits(2):ck(int(h==y)==int((xor(x),d)==y),'indicator tests pull back pointwise')
        ck(all(c.output(x)==r.output(x) for x,d in support),'pointwise actual controller transfer correlated or independent')
    ck(uniform(x for x,d in good)!=uniform(x for x,d in correlated),'actual correlated early input not product preparation')
    # Counterexample to product of marginal early and delayed laws: keep actual
    # marginal d fair but redraw it independently, losing the crucial coupling.
    redraw=[(x,fresh) for x,d in correlated for fresh in (0,1)]
    badlaw=uniform((c.output(x)[0],d) for x,d in redraw)
    ck(badlaw!=target and sum(p for (pbit,d),p in badlaw.items() if pbit!=d)==F(1,2),
       'independently redrawn delayed marginal unsound')
    return {'two_tile_independent_support':len(good),'correlated_support':len(correlated),
            'same_joint_hazard':0,'independent_delay_redraw_hazard':'1/2'}


def main():
    result={'status':'PASS','scope':'finite original-C5 instantiation support, not general C5 kernel proof',
            'terms':verify_terms(),'representative':verify_representative(),'same_joint_w':verify_same_joint_w()}
    result['assertions']=N
    here=Path(__file__).resolve().parent
    names=['c5_controller_instantiation.md','verify_c5_instantiation.py']
    result['sha256']={name:hashlib.sha256((here/name).read_bytes()).hexdigest() for name in names}
    path=here/'verification_c5_instantiation.json';path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
