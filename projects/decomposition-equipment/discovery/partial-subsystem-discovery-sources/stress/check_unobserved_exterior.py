"""Exact-law observable-table QA; global chain is generator ONLY.
Learner sees noisy tensors and logged regime, not hidden states or channels.
Not a finite-sample or arbitrary-size implementation claim.
"""
import itertools, json
from pathlib import Path
import numpy as np
def recover_three_view(t, rng):
    m12 = t.sum(axis=2)
    u, s, vt = np.linalg.svd(m12, full_matrices=False)
    rank = int(np.sum(s > 1e-11))
    u, v = u[:, :rank], vt[:rank].T
    middle = u.T @ m12 @ v
    inv = np.linalg.inv(middle)
    ops = [u.T @ t[:, :, k] @ v @ inv for k in range(t.shape[2])]
    best = None
    for _ in range(40):
        h = rng.normal(size=t.shape[2])
        op = sum(w * x for w, x in zip(h, ops))
        vals, vec = np.linalg.eig(op)
        if max(np.max(np.abs(vals.imag)), np.max(np.abs(vec.imag))) > 1e-8:
            continue
        vals, vec = vals.real, vec.real
        gap = min(abs(x - y) for j, x in enumerate(vals) for y in vals[j+1:])
        if best is None or gap > best[0]:
            best = (gap, vec)
    assert best is not None
    vec = best[1]
    a = u @ vec
    a /= a.sum(axis=0, keepdims=True)
    vinv = np.linalg.inv(vec)
    c = np.array([np.diag(vinv @ op @ vec) for op in ops])
    weighted_bt = np.linalg.pinv(a) @ m12
    weights = weighted_bt.sum(axis=1)
    b = (weighted_bt / weights[:, None]).T
    reconstruction = np.einsum('z,az,bz,cz->abc', weights, a, b, c)
    assert min(a.min(), b.min(), c.min(), weights.min()) > -1e-8
    return [a, b, c], weights, float(np.max(abs(reconstruction - t)))


def support_components(joint, threshold=1e-7):
    ka, kb = joint.shape
    adj = [[] for _ in range(ka + kb)]
    for a, b in zip(*np.nonzero(joint > threshold)):
        adj[a].append(ka + b)
        adj[ka + b].append(a)
    labels = np.full(ka + kb, -1, dtype=int)
    count = 0
    for start in range(ka + kb):
        if labels[start] >= 0:
            continue
        labels[start] = count
        stack = [start]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if labels[y] < 0:
                    labels[y] = count
                    stack.append(y)
        count += 1
    return count, labels[:ka], labels[ka:]



def run(N,seed=197):
 rng=np.random.default_rng(seed+N)
 states=np.array(list(itertools.product([0,1],repeat=N+5)))
 # a,b,y,h1,...,hN,delay,w; oracle only
 a,b,y=states[:,:3].T; hs=states[:,3:3+N]; v=hs[:,0]; d=states[:,-2]
 S=len(states); mats=[]
 for r in [0,1]:
  T=np.zeros((S,S))
  for j,s in enumerate(states):
   aa,bb,yy=s[:3]; h=s[3:3+N]; dd=s[-2]; vv=h[0]
   pz=.15+.10*h[-1]+.35*r
   for z in [0,1]:
    ps=[.10+.10*aa+.15*bb+.20*dd+.05*aa*bb,
        .15+.10*bb+.20*aa+.15*vv+.05*aa*vv,
        .10+.10*yy+.10*aa+.10*vv+.40*z,
        .10+.15*h[0]+.10*h[1]+.15*z+.10*aa]
    for i in range(1,N):
     nxt=h[(i+1)%N]
     ps.append(.15+.15*h[i]+.10*nxt+.10*aa+.05*h[i]*nxt)
    ps += [float(vv),.4]
    ps=np.array(ps)
    T[j]+=(pz if z else 1-pz)*np.prod(np.where(states,ps,1-ps),axis=1)
  assert np.max(abs(T.sum(1)-1))<1e-12
  mats.append(T)
 T=sum(mats)/2; pi=np.full(S,1/S)
 for it in range(2000):
  nxt=pi@T
  if max(abs(nxt-pi))<1e-15: break
  pi=nxt
 assert np.max(abs(pi@T-pi))<1e-13
 # Hide labels before observable table construction.
 perm1=rng.permutation(8); perm2=rng.permutation(4)
 p1=perm1[4*a+2*b+y]; p2=perm2[2*b+v]
 inc1=np.eye(8)[p1]; inc2=np.eye(4)[p2]
 channels=[]; recovered=[]; recon=[]
 for ids,k in [(p1,8),(p2,4)]:
  E=[]
  for _ in range(3):
   e=rng.uniform(.03,.1,(10,k)); e[np.arange(k),np.arange(k)]+=1
   e/=e.sum(0); E.append(e)
  weights=np.bincount(ids,weights=pi,minlength=k)
  obs=np.einsum('z,az,bz,cz->abc',weights,*E)
  rec,ww,err=recover_three_view(obs,rng)
  channels.append(E); recovered.append(rec); recon.append(err)
 # Joint latent law (P1_current,P2_current,P2_previous,P1_next,R).
 prev_by_curr=(inc2.T*pi)@T # previous patch versus current whole state
 latent=np.zeros((8,4,4,8,2))
 for r in [0,1]:
  future=mats[r]@inc1
  for s in range(S):
   latent[p1[s],p2[s],:,:,r]+=.5*np.outer(prev_by_curr[:,s],future[s])
 e1=channels[0][0]; e2=channels[1][0]
 obs=np.einsum('ijklr,ai,bj,ck,dl->abcdr',latent,e1,e2,e2,e1,optimize=True)
 # Selected task channel is an observed Bernoulli readout, not a supplied latent coordinate.
 task_joint=inc1.T@(pi[:,None]*np.array([.8-.6*a,.2+.6*a]).T)
 task_observed=e1@task_joint
 # LEARNER START: only observable table, tensors/recovered calibrations.
 l1=np.linalg.pinv(recovered[0][0]); l2=np.linalg.pinv(recovered[1][0])
 table=np.einsum('abcdr,ia,jb,kc,ld->ijklr',obs,l1,l2,l2,l1,optimize=True)
 table[abs(table)<1e-13]=0
 assert table.min()>-1e-10
 overlap=table.sum(axis=(2,3,4))
 count,shared1,shared2=support_components(overlap)
 assert count==2
 mass=table.sum(3)
 valid=mass>1e-10
 rows=np.moveaxis(table,3,-1)[valid]/mass[valid,None]
 # Enumerate all private 2x2 charts in each recovered b fibre.
 fibres=[np.where(shared1==j)[0] for j in [0,1]]
 assert all(len(f)==4 for f in fibres)
 survivors=[]; bestbad=1.
 for left in itertools.permutations(range(4)):
  for right in itertools.permutations(range(4)):
   chart=np.empty((8,3),int)
   for bb,perm in enumerate([left,right]):
    for ii,c in enumerate(fibres[bb]): chart[c]=[bb,perm[ii]//2,perm[ii]%2]
   marg=[rows@np.eye(2)[chart[:,i]] for i in range(3)]
   pred=np.ones_like(rows)
   for i in range(3): pred*=marg[i][:,chart[:,i]]
   err=np.max(abs(pred-rows))
   if err<1e-8: survivors.append(chart)
   else: bestbad=min(bestbad,float(err))
 assert len(survivors)==8, len(survivors)
 chart=survivors[0]
 task_decoded=l1@task_observed
 task_response=task_decoded[:,1]/task_decoded.sum(1)
 task_axes=[axis for axis in range(3) if all(np.ptp(task_response[chart[:,axis]==z])<1e-8 for z in [0,1])]
 assert len(task_axes)==1
 # Paired regime rows given SAME old context, then full JOINT quotient.
 cond=np.moveaxis(table,3,-1)/np.maximum(mass[...,None],1e-100)
 paired=valid[...,0]&valid[...,1]
 diff=cond[:,:,:,1,:]-cond[:,:,:,0,:]
 gaps=[float(np.max(abs((diff@np.eye(2)[chart[:,i]])[paired]))) for i in range(3)]
 stable=[i for i,g in enumerate(gaps) if g<1e-8]
 assert len(stable)==2 and abs(max(gaps)-.14)<1e-8,gaps
 assert task_axes[0] in stable
 jointids=2*chart[:,stable[0]]+chart[:,stable[1]]
 jointgap=float(np.max(abs((diff@np.eye(4)[jointids])[paired])))
 assert jointgap<1e-8
 # Discover a one-bit port quotient, including its old-memory use. Do not
 # supply which of four port states share the same v. The b overlap fixes
 # fibres, but permits independent flips within them (four candidates).
 portfibres=[np.where(shared2==j)[0] for j in [0,1]]
 port_survivors=[]
 core_rows=cond@np.eye(4)[jointids]
 for flips in itertools.product([0,1],repeat=2):
  port=np.empty(4,int)
  for bb in [0,1]:
   port[portfibres[bb]]=[flips[bb],1-flips[bb]]
  groups={}; residual=0.
  for i,j,k,r in zip(*np.nonzero(valid)):
   key=(int(chart[i,stable[0]]),int(chart[i,stable[1]]),int(port[j]),int(port[k]))
   row=core_rows[i,j,k,r]
   if key in groups: residual=max(residual,float(np.max(abs(row-groups[key]))))
   else: groups[key]=row
  if residual<1e-8: port_survivors.append((port,groups))
 assert len(port_survivors)==2,len(port_survivors)
 groups=port_survivors[0][1]
 assert len(groups)==16
 # Every proposed retained input is essential: including the delayed port.
 essential_gaps=[]
 for axis in range(4):
  gap=0.
  for key,row in groups.items():
   other=list(key); other[axis]=1-other[axis]
   gap=max(gap,float(np.max(abs(row-groups[tuple(other)]))))
  essential_gaps.append(gap)
 assert min(essential_gaps)>.05
 # Core conditional law ignores old decoy coordinate, even conditioned on
 # arbitrary finite old sensor contexts. Match oracle only AFTER discovery.
 oraclemap=[]
 for e,rec in zip(channels,recovered):
  oraclemap.append(np.argmin(np.max(abs(e[0][:,:,None]-rec[0][:,None,:]),axis=0),axis=0))
 # Recover labels for QA, not used above.
 invperm=np.argsort(perm1); actual=invperm[oraclemap[0]]
 expected=np.array([(x//4,(x//2)%2,x%2) for x in actual])
 for i in stable:
  assert any(np.all(chart[:,i]==expected[:,j]) or np.all(chart[:,i]==1-expected[:,j]) for j in [0,1])
 return dict(exterior_bits=N,oracle_states=S,calibration_max_error=max(recon),
             discovered_patch_cardinalities=[8,4],shared_components=count,
             private_charts_tested=576,product_charts_surviving=len(survivors),
             task_anchor_identified=True,
             nearest_rejected_product_residual=bestbad,regime_marginal_gaps=gaps,
             joint_core_regime_gap=jointgap,port_quotients_tested=4,port_quotients_surviving=len(port_survivors),
             essential_core_current_delayed_port_gaps=essential_gaps,unobserved_exterior_states=2**(N-1),
             observable_table_entries=int(obs.size))

if __name__=='__main__':
 results=[run(n) for n in [2,3,5]]
 # Passive obstruction: full IID law identical, replacement behavior differs.
 assert abs(.5*.2+.5*.6-.4)<1e-15
 assert abs((.9-.8*.6)-(.9-.8*.25)+.28)<1e-15
 results.append({'joint_only_regime_agreement_gap':-.28,'individual_regime_gaps':[0.,0.],
                 'passive_indistinguishable_output_p':.4,
                 'replacement_output_p':[.2+.4*.1,.2+.4*.9],
                 'autonomous_output_p_under_both_replacements':.4})
 print(json.dumps(results,indent=2))
 Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2)+'\n')
