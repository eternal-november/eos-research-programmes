#!/usr/bin/env python3
"""Exact finite-fair-bit implementation of the frozen empirical source kernels.

No learner, model, data, or probability estimate is changed. Each independent source
block uses its OWN fresh bit segment. Owners share only projections of that block's
sampled row. A FairBits source is an explicit callable returning independent bits;
NumPy supplies reproducible pseudo-fair test bits, not a physical entropy claim.
Usage: python check_exact_source_sampler.py runs/n12 runs/n24 runs/n48 runs/n96
"""
import bisect,json,math,sys
from fractions import Fraction
from pathlib import Path
import numpy as np
import check_growing_memory_environment as c

class FairBits:
    def __init__(self,seed):self.rng=np.random.default_rng(seed);self.used=0
    def __call__(self):
        self.used+=1
        return int(self.rng.integers(0,2))

def compile_exact_sampler(kernel):
    counts=kernel['counts'];N=sum(counts)
    assert N>0 and (N&(N-1))==0
    b=N.bit_length()-1;endpoints=[];end=0
    for count,q in zip(counts,kernel['probabilities']):
        assert isinstance(count,int) and count>=0
        assert Fraction(count,N)==Fraction.from_float(q)
        end+=count;endpoints.append(end)
    assert end==N
    # Exact finite partition certificate: disjoint consecutive integer intervals
    # cover [0,N), with row-r preimage cardinality equal to frozen empirical count.
    start=0
    for r,(count,end) in enumerate(zip(counts,endpoints)):
        assert end-start==count
        if count:
            assert bisect.bisect_right(endpoints,start)==r
            assert bisect.bisect_right(endpoints,end-1)==r
        start=end
    return {'bits':b,'N':N,'endpoints':endpoints,'rows':kernel['rows']}

def sample_exact(compiled,next_fair_bit):
    index=0
    for _ in range(compiled['bits']):
        bit=next_fair_bit();assert bit in (0,1)
        index=2*index+bit
    # Every index has exactly probability 2^-bits. No rejection, rounding, or
    # continuous uniform random number is needed.
    row=bisect.bisect_right(compiled['endpoints'],index)
    return np.array(compiled['rows'][row],dtype=int)

def check(path):
    path=Path(path);candidate=json.loads((path/'executable_candidate.json').read_text())
    models=candidate['mean'];memory=candidate['memory_transducers'];kernels=candidate['joint_innovation_interfaces'];n=len(models)
    samplers=[compile_exact_sampler(k) for k in kernels]
    per_tick=sum(s['bits'] for s in samplers)
    bits=FairBits(600001+n);checks=0
    for policy in ('neighbor_sign','alternating_threshold','cross_group_majority','history_switch'):
        A=c.compile_description([i%3 for i in range(n)],models,memory,kernels,n)
        B=c.compile_description([(i//3)%4 for i in range(n)],models,memory,kernels,n)
        history=np.full((c.L,n),-1,dtype=np.int8);last=np.zeros(n);prev=np.zeros(n)
        for t in range(128):
            if policy=='neighbor_sign':action=np.where(np.roll(last,1)>=0,-1,1)
            elif policy=='alternating_threshold':action=np.where(last+np.roll(last,3)>t%7-3,1,-1)
            elif policy=='cross_group_majority':action=np.where(np.roll(last,2)+np.roll(last,7)+np.roll(last,11)>=0,1,-1)
            else:action=np.where((last-prev)*np.roll(last,5)>=0,1,-1)
            before=bits.used;events={}
            for j,sampler in enumerate(samplers):
                # Separate calls consume separate fresh segments; never reuse an
                # index across groups claimed to be stochastically independent.
                group_before=bits.used;events[j]=sample_exact(sampler,bits)
                assert bits.used-group_before==sampler['bits']
            assert bits.used-before==per_tick
            outA=c.execute_description(A,action,events,models,memory,n)
            outB=c.execute_description(B,action,events,models,memory,n)
            ah=np.vstack([history,action]);raw=np.array([c.scalar_value(m,ah,n) for m in models])
            for j,k in enumerate(kernels):raw[k['members']]+=events[j]
            assert np.array_equal(outA,outB) and np.array_equal(outA,raw)
            checks+=n;prev,last=last,outA;history=ah[-c.L:]
    assert bits.used==4*128*per_tick
    return {'n':n,'frozen_candidate_sha256':c.sha(path/'executable_candidate.json'),
        'all_cumulative_interval_certificates_passed':True,
        'innovation_blocks':len(kernels),'fair_bits_per_block_per_tick':[s['bits'] for s in samplers],
        'fair_bits_per_global_tick':per_tick,
        'bounded_draws_no_rejection_or_continuous_uniform':True,
        'independent_blocks_get_disjoint_fresh_bit_segments':True,
        'maximum_joint_row_label_bits':max((len(s['rows'])-1).bit_length() for s in samplers),
        'one_noise_projection_bits':1,'one_projection_per_readout_global_bits':n,
        'group_outcome_label_bits_total_if_sent_once':sum((len(s['rows'])-1).bit_length() for s in samplers),
        'feedback_policies_tested':4,'steps_each':128,'owner_local_vs_raw_equalities':checks,
        'test_bit_calls':bits.used,
        'exact_probability_reason':'an interval of count[g,r] among 2^17 equally likely bit strings; exact probability equals frozen count[g,r]/131072',
        'resource_scope':'source innovation sampling and noise projection only; action broadcasts, memory updates and transport fanout remain separately charged'}

if __name__=='__main__':print(json.dumps([check(p) for p in sys.argv[1:]],indent=2))
