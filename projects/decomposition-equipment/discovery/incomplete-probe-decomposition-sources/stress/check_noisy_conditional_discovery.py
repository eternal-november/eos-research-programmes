"""Standalone exact-observation-law QA. No finite-sample claim.
Three-view spectral helper copied with attribution from earlier local mechanism
QA (check_hidden_patch_discovery.py); all code is vendored here.
"""
import itertools,json
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


def parts(xs):
 if not xs:yield [];return
 x,*rest=xs
 for p in parts(rest):
  yield [[x]]+[b[:] for b in p]
  for j in range(len(p)):
   q=[b[:] for b in p];q[j]=[x]+q[j];yield q

def run(seed=1038):
 rng=np.random.default_rng(seed)
 # ORACLE ONLY: actual latent coordinates, pair chain, and unknown sensors.
 hidden=list(itertools.product([0,1],repeat=3))
 states=[[hidden[j] for j in rng.permutation(8)] for _ in range(2)]
 U=np.array([[1.,0.],[-1.,0.],[0.,1.],[0.,-1.]])
 Z=np.array([[0,0],[1,0],[-1,0],[0,1],[0,-1]],float)
 tau=.75; source=np.array([1-tau,*([tau/4]*4)])
 H=np.array([[1.3,.2],[.1,.85]])
 amps=[.025*H,.025*np.linalg.inv(H).T]
 def raw(c,outputs,A):
  a,b,y=c;w=np.array([2+a+2*a*b,2+b,2+(a^b),2+2*b+a*b],float);base=w/w.sum()
  s=1+.2*a+.15*b
  out=[]
  for ap,bp,yp in outputs:
   d=.2+.1*y+.05*ap+.03*bp+.02*a
   out.append((base[2*ap+bp]+s*(Z@A.T@U[2*ap+bp]))*(d if yp else 1-d))
  return np.array(out).T
 K=[np.array([raw(x,states[i],amps[i]) for x in states[i]]) for i in range(2)]
 joint_kernel=np.einsum('z,xza,yzb->xyab',source,*K)
 P=joint_kernel.reshape(64,64)
 assert P.min()>0 and abs(P.sum(axis=1)-1).max()<1e-12
 stationary=np.ones(64)/64
 for _ in range(10000):
  nxt=stationary@P
  if abs(nxt-stationary).max()<1e-16:stationary=nxt;break
  stationary=nxt
 assert abs(stationary@P-stationary).max()<1e-14
 old=stationary.reshape(8,8); marg=[old.sum(axis=1),old.sum(axis=0)]
 emissions=[]
 for _ in range(2):
  es=[]
  for _ in range(3):
   E=rng.gamma(1.2,1.,size=(10,8))+.15
   E/=E.sum(axis=0,keepdims=True);es.append(E)
  emissions.append(es)
 triples=[np.einsum('z,az,bz,cz->abc',marg[i],*emissions[i]) for i in range(2)]
 temporal_latent=old[:,:,None,None]*joint_kernel
 temporal=np.einsum('xyab,px,qy,ra,sb->pqrs',temporal_latent,emissions[0][0],emissions[1][0],emissions[0][0],emissions[1][0],optimize=True)
 task_probs=[np.array([.15+.7*x[0] for x in ss]) for ss in states]
 task_tables=[]
 for i in range(2):
  tasklaw=np.stack([1-task_probs[i],task_probs[i]],axis=1)
  task_tables.append(emissions[i][0]@(marg[i][:,None]*tasklaw))

 # LEARNER BOUNDARY: only observed triples, temporal10^4 tensor, current
 # sensor/taskbit joint tables. No latent K, F, coordinates, or q supplied.
 learned=[];weights=[];errors=[]
 for t in triples:
  es,w,err=recover_three_view(t,rng);learned.append(es);weights.append(w);errors.append(err)
 ranks=[e[0].shape[1] for e in learned]
 assert ranks==[8,8]
 dec=[np.linalg.pinv(es[0]) for es in learned]
 recovered=np.einsum('pqrs,xp,yq,ar,bs->xyab',temporal,dec[0],dec[1],dec[0],dec[1],optimize=True)
 recovered_old=recovered.sum(axis=(2,3))
 assert recovered.min()>0 and recovered_old.min()>0
 recovered_kernel=recovered/recovered_old[:,:,None,None]
 task_values=[];partitions=[];num_conditional=[];rank_residual=[];autocount=[]
 learned_B=[];learned_D=[]
 for i in range(2):
  # Swap moduleaxes so learner procedure is identical for both modules.
  kernel=recovered_kernel if i==0 else recovered_kernel.transpose(1,0,3,2)
  # Marginal old_i→next_i is independent of reference old_j, checked below.
  B=kernel[:,0].sum(axis=2)
  assert abs(kernel.sum(axis=3)-B[:,None,:]).max()<1e-8
  Bj=kernel[0,0].sum(axis=0)
  D=kernel[:,0]-B[:,:,None]*Bj[None,None,:]
  assert abs(kernel[:,0].sum(axis=1)-Bj[None,:]).max()<1e-8
  rank_residual.append(int(np.sum(np.linalg.svd(D[0],compute_uv=False)>1e-9)))
  learned_B.append(B);learned_D.append(D)
  tj=dec[i]@task_tables[i]
  tv=tj[:,1]/tj.sum(axis=1);task_values.append(tv)
  values=sorted(tv);centers=[]
  for v in values:
   if not centers or abs(v-centers[-1])>1e-7:centers.append(v)
  assert len(centers)==2
  task=np.argmin(abs(tv[:,None]-np.array(centers)[None,:]),axis=1)
  candidates=[p+q for p in parts([int(x) for x in np.flatnonzero(task==0)]) for q in parts([int(x) for x in np.flatnonzero(task==1)])]
  def conditional(p):
   for oldblock in p:
    for x,y in itertools.combinations(oldblock,2):
     for t in p:
      if abs(B[x,t].sum()-B[y,t].sum())>1e-8:return False
      if abs(D[x,t].sum(axis=0)-D[y,t].sum(axis=0)).max()>1e-8:return False
   return True
  valid=[p for p in candidates if conditional(p)]
  coarse=[p for p in valid if len(p)==min(map(len,valid))]
  assert len(candidates)==225 and len(coarse)==1 and len(coarse[0])==4
  autos=[p for p in valid if all(abs(D[x,t].sum(axis=0)).max()<1e-8 for x,t in itertools.product(range(8),p))]
  assert not autos
  partitions.append(coarse[0]);num_conditional.append(len(valid));autocount.append(len(autos))

 # ORACLE VALIDATION ONLY, AFTER all learner outputs are fixed.
 maps=[];emission_errors=[]
 for i in range(2):
  cost=np.linalg.norm(learned[i][0][:,:,None]-emissions[i][0][:,None,:],axis=0)
  mp=cost.argmin(axis=1);assert len(set(mp))==8;maps.append(mp)
  emission_errors.append(float(cost[np.arange(8),mp].max()))
  true_groups={frozenset(j for j in range(8) if states[i][mp[j]][:2]==(a,b)) for a,b in itertools.product([0,1],repeat=2)}
  assert {frozenset(b) for b in partitions[i]}==true_groups
  assert abs(task_values[i]-task_probs[i][mp]).max()<1e-8
 aligned=joint_kernel[np.ix_(maps[0],maps[1],maps[0],maps[1])]
 row_error=float(abs(recovered_kernel-aligned).max())
 assert row_error<1e-8
 return {'status':'PASS','seed':seed,'oracle_pair_states':64,'observed_sensor_alphabet':10,'learned_raw_cardinalities':ranks,'learned_response_ranks':rank_residual,'coarsest_conditional_partitions':partitions,'coarsest_cardinalities':[len(p) for p in partitions],'conditional_partition_counts':num_conditional,'autonomous_partition_counts':autocount,'learned_task_probability_levels':[sorted(set(np.round(v,8))) for v in task_values],'three_view_tensor_error':max(errors),'sensor_alignment_error_validation_only':max(emission_errors),'joint_conditional_kernel_error_validation_only':row_error,'minimum_recovered_stationary_context_mass':float(recovered_old.min()),'minimum_actual_transition_probability':float(P.min()),'raw_temporal_tensor_entries':int(temporal.size),'scope':'Exact stationary observation-law QA; unknown calibration recovered numerically. No latent state preparation or trajectory clones. No finite-sample stability or arbitrary omitted effects certification.'}

if __name__=='__main__':
 import sys
 if '--multiseed' in sys.argv:
  runs=[run(seed) for seed in [1038,1041,1093,2026,731]]
  result={'status':'PASS','seeds':[r['seed'] for r in runs],'max_joint_kernel_error':max(r['joint_conditional_kernel_error_validation_only'] for r in runs),'all_coarsest_cardinalities':[r['coarsest_cardinalities'] for r in runs],'all_response_ranks':[r['learned_response_ranks'] for r in runs]}
  dest=Path(__file__).with_name('Noisy_Conditional_Discovery_Multiseed_QA.json')
 else:
  result=run();dest=Path(__file__).with_suffix('.json')
 dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
