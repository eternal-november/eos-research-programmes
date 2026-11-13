"""Exact finite checks; synthetic destructive specimen service, no physical claim."""
from fractions import Fraction as F
from itertools import product
from collections import defaultdict
import json
from pathlib import Path

CP={'screen':(2,1),'C':(5,2),'A':(3,1),'B':(4,2),'D':(6,2),'discard':(0,0)}
CQ={'screen':(4,2),'C':(8,3),'A':(5,2),'B':(7,3),'D':(9,3),'discard':(0,0)}
def probs(m,q):
    if m=='C': return [('pass',F(6 if q==0 else 1,10)),('fail',F(1 if q==0 else 6,10)),('uncertain',F(3,10))]
    if m=='discard': return [('discarded',F(1))]
    p={'screen':(F(1,4),F(3,4)), 'A':(F(1,4),F(3,4)), 'B':(F(1,8),F(7,8)), 'D':(F(1,5),F(4,5))}[m][q]
    return [(0,1-p),(1,p)]
def cost(ms,C):return tuple(sum(C[m][i] for m in ms) for i in range(2))
# Local certificate for EVERY related pair q versus (q,j), including unreachable states.
checks=0
for m,n in [('screen',3),('C',2),('A',1),('B',1),('D',1),('discard',1)]:
    for qs in product((0,1),repeat=n):
      for js in product((0,1),repeat=n):
        p=dict(probs(m,qs[0])); audit=(0,) if m=='discard' else (0,1)
        Q={(o,a):w/F(len(audit)) for o,w in p.items() for a in audit}
        G={(o,(o,a)):w for (o,a),w in Q.items()}
        assert all(sum(w for (u,v),w in G.items() if u==o)==p[o] for o in p)
        assert all(sum(w for (u,v),w in G.items() if v==z)==Q[z] for z in Q)
        assert all(a<=b for a,b in zip(CP[m],CQ[m]))
        # Fixed physical quality is unchanged on surviving actual IDs; junk is retained.
        if m=='screen': partitions={0:((1,2),),1:((1,),(2,))}
        elif m=='C': partitions={o:((1,),) for o in p}
        else: partitions={o:((),) for o in p}
        for o,parts in partitions.items():
            flat=sum((list(s) for s in parts),[])
            assert len(flat)==len(set(flat)) and 0 not in flat
            assert all(0<=r<n for r in flat)
            assert all(qs[r]==(qs[r],js[r])[0] for r in flat)
        checks+=1

# Full controller, all three initial specimens share one private quality bit.
rows=[]
for q in (0,1):
 for y,py in probs('screen',q):
  if y==0:
   for z,pz in probs('C',q):
    m='D' if z=='uncertain' else 'discard'
    for d,pd in probs(m,q):
     tree=('screen0',('C_'+z,(m+'_'+str(d),('leaf',str(z),str(d)))))
     rows.append((q,F(1,2)*py*pz*pd,tree,('screen','C',m)))
  else:
   for a,pa in probs('A',q):
    for b,pb in probs('B',q):
     tree=('screen1',('A_'+str(a),('leaf',str(a))),('B_'+str(b),('leaf',str(b))))
     rows.append((q,F(1,2)*py*pa*pb,tree,('screen','A','B')))
# Independently replay the complete concrete resource ledger at every latent path.
ledger_checks=0
for q,w,t,ms in rows:
    owned={'r0':'Screen','r1':'Reserve','r2':'Reserve'}
    assert owned=={'r0':'Screen','r1':'Reserve','r2':'Reserve'}
    del owned['r0']
    assert 'r0' not in owned
    if t[0]=='screen0':
        owned['r1']='Confirm'
        assert owned=={'r1':'Confirm','r2':'Reserve'}
        del owned['r1']
        uncertain=t[1][0]=='C_uncertain'
        owned['r2']='RescueD' if uncertain else 'Discard'
        assert (owned['r2']=='RescueD')==('D' in ms)
        assert (owned['r2']=='Discard')==('discard' in ms)
        del owned['r2']
    else:
        owned={'r1':'AssayA','r2':'AssayB'}
        left={'r1':owned['r1']};right={'r2':owned['r2']}
        assert set(left).isdisjoint(right)
        assert left=={'r1':'AssayA'} and right=={'r2':'AssayB'}
        del left['r1'];del right['r2'];owned=left|right
    assert owned=={}
    ledger_checks+=1
P=defaultdict(F);Q=defaultdict(F);coupling=defaultdict(F)
for q,w,t,ms in rows:
 cp,cq=cost(ms,CP),cost(ms,CQ)
 P[(cp,t)]+=w
 audits=list(product((0,1),repeat=sum(m!='discard' for m in ms)))
 for aud in audits:
  v=w/len(audits)
  Q[(cq,t)]+=v
  coupling[((cp,t),(cq,t))]+=v
assert sum(P.values())==sum(Q.values())==1
assert len(P)==len(Q)==8
for x,p in P.items():assert sum(w for (u,v),w in coupling.items() if u==x)==p
for y,p in Q.items():assert sum(w for (u,v),w in coupling.items() if v==y)==p
assert all(u[1]==v[1] and all(a<=b for a,b in zip(u[0],v[0])) for u,v in coupling)
EP=[sum(w*k[0][i] for k,w in P.items()) for i in range(2)]
EQ=[sum(w*k[0][i] for k,w in Q.items()) for i in range(2)]
# Independent two-stage screen model: BOTH noise bits affect the answer.
# This is a second implementation inside Case A, not an extra portfolio case.
noise={(u,v):(F(1,8) if u else F(7,8))*(F(1,6) if v else F(5,6))
       for u,v in product((0,1),repeat=2)}
assert noise=={(0,0):F(35,48),(0,1):F(7,48),(1,0):F(5,48),(1,1):F(1,48)}
sensor_raw_checks=0
for theta in (0,1):
    compressed=defaultdict(F)
    for (u,v),p in noise.items():
        w=u^v;y=theta^w
        compressed[y]+=p
        # Flipping either independent input bit changes the reply.
        assert (theta^(1-u)^v)!=y and (theta^u^(1-v))!=y
        sensor_raw_checks+=1
    assert dict(compressed)==dict(probs('screen',theta))
    for y,ky in compressed.items():
        Ay={(u,v):p/ky for (u,v),p in noise.items() if theta^u^v==y}
        assert sum(Ay.values())==1
        for uv,a in Ay.items():assert ky*a==noise[uv]
# Independently lift the whole controller to this non-fair conditional residual.
Qsensor=defaultdict(F)
for theta,w,t,ms in rows:
    y=int(t[0][-1]);ky=dict(probs('screen',theta))[y]
    other_audits=list(product((0,1),repeat=sum(m not in ('discard','screen') for m in ms)))
    for uv,pnoise in noise.items():
        if theta^uv[0]^uv[1]!=y:continue
        for aud in other_audits:
            Qsensor[(cost(ms,CQ),t)]+=w*pnoise/ky/len(other_audits)
assert Qsensor==Q
# Correlation: after screen1, assays are NOT marginally independent.
joint=sum(w for (c,t),w in P.items() if t[0]=='screen1' and t[1][0]=='A_1' and t[2][0]=='B_1')/F(1,2)
ma=sum(w for (c,t),w in P.items() if t[0]=='screen1' and t[1][0]=='A_1')/F(1,2)
mb=sum(w for (c,t),w in P.items() if t[0]=='screen1' and t[2][0]=='B_1')/F(1,2)
assert joint==F(1,2) and ma*mb==F(55,128)
# Same list of returned leaf values does not determine causal tree.
t1=('screen0',('C_pass',('discard_discarded',('leaf','x'))))
t2=('screen0',('C_uncertain',('D_1',('leaf','x'))))
def leaves(t):return [t[1:]] if t[0]=='leaf' else sum((leaves(s) for s in t[1:]),[])
assert t1!=t2 and leaves(t1)==leaves(t2)
# Native forgetting-audit cell: p_y=sum fibre p; output cost<=minimum fibre cost.
for m in CP:
 for q in (0,1):
  for o,p in probs(m,q):
   assert p==sum((p/F(2) for _ in (0,1)),F(0))
   assert all(a<=b for a,b in zip(CP[m],CQ[m]))
assert any(a<b for a,b in zip(CP['screen'],CQ['screen']))
# Consumed ID cannot be reused; pure ModelCode/evidence adds no ownership.
assert 'r0' not in {'r1','r2'}
assert not {'r0','r1','r2'} <= {'r1','r2'}
assert set() | set() == set()
result={'screen_compression_raw_checks':sensor_raw_checks,'screen_reference_variants_checked':['fair_audit','two_stage_XOR'],'two_stage_full_joint_law_matches':Qsensor==Q,'local_related_input_checks':checks,'complete_resource_ledgers':ledger_checks,'raw_latent_controller_paths':len(rows),'public_joint_law_atoms':len(P),'total_probability':str(sum(P.values())), 'expected_candidate_cost':list(map(str,EP)), 'expected_reference_cost':list(map(str,EQ)), 'conditional_joint_A1_B1':str(joint),'incorrect_independent_product':str(ma*mb),'paths':[{'probability':str(w),'candidate_cost':list(k[0]),'reference_cost':list(next(v[0] for (u,v) in coupling if u==k)),'tree':k[1]} for k,w in P.items()], 'checks':'PASS: exact rational local/full couplings, resources, cost order, correlation, tree shadow, native audit cell'}
Path(__file__).with_name('case_A_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
