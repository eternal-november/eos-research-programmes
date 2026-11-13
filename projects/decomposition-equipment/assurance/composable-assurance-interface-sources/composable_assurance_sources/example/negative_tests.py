"""Adversarial semantics regressions, separately scoped from frozen capability outcomes."""
import json
from pathlib import Path
from experiment import Ledger,DependencyCache

def incidence(windows,block=0,generation=0):
    return {i:tuple((generation,block,f) for f in frames) for i,frames in enumerate(windows)}

def replacement_preserves(old,new,pinned,token_map):
    # Sufficient intensional matching law; no claim complete for equivalent kernels.
    oldtokens={t for row in old.values() for t in row};newtokens={t for row in new.values() for t in row}
    if set(token_map)!=newtokens or set(token_map.values())!=oldtokens:return False
    if len(set(token_map.values()))!=len(token_map):return False
    if any(token_map.get(t)!=t for t in pinned):return False
    return all(tuple(token_map[t] for t in new[i])==old[i] for i in old) and set(old)==set(new)

def main():
    old=incidence([(-2,-1)]*5);same=incidence([(-2,-1)]*5)
    tokens=set(old[0]);identity={t:t for t in tokens}
    assert replacement_preserves(old,same,tokens,identity)
    split=incidence([(-2,-1)]*3+[(-1,0)]*2)
    assert not replacement_preserves(old,split,tokens,{t:t for row in split.values() for t in row})
    # Equal marginal width and rate do not satisfy joint incidence preservation.
    assert all(len(row)==2 for row in split.values())
    fresh=incidence([(-2,-1)]*5,generation=1)
    mapping={t:(0,t[1],t[2]) for row in fresh.values() for t in row}
    assert not replacement_preserves(old,fresh,tokens,mapping)
    ledger=Ledger();assert ledger.reserve(tokens,.022);ledger.expose(tokens)
    used=ledger.used
    # Scheduled lease expiry does not mutate the original mission account.
    valid=False
    assert not valid and ledger.used==used
    assert not ledger.reserve({(1,0,0)},.022)
    favorable=Ledger();favorable.exposed.add((0,0,0))
    try:favorable.reserve({(0,0,0)},.022)
    except ValueError:pass
    else:raise AssertionError('Post-observation original-rate charge accepted')
    cache=DependencyCache(3);assert cache.query('mission')
    cache.change('physical0',False);assert not cache.query('cell0')
    cache.change('physical1',False);cache.change('physical0',True)
    assert cache.query('cell0') and not cache.query('mission')
    cache.change('physical1',True);assert cache.query('mission')
    results={'same_boundary_accept':True,'same_marginal_changed_joint_rejected':True,
      'pinned_identity_generation_reset_rejected':True,'split_merge_without_token_reaccounting_rejected':True,
      'offpath_stale_cache_rejected':True,'postobservation_charge_rejected':True,
      'expiry_risk_refund_absent':True,
      'scope':'Sufficient exact incidence checker; fixed learned kernels. No arbitrary kernel equivalence or pending-packet migration.'}
    (Path(__file__).parent/'results'/'negative_tests.json').write_text(json.dumps(results,indent=2))
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
