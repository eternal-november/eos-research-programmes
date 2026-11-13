"""Exact rational fixtures for persistent hidden memory and parity closure."""
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
import json

bits=lambda n:list(product((0,1),repeat=n))
def chi(z): return 1 if sum(z)%2==0 else -1
def prob_noise(e,eps):
    p=Q(1)
    for b in e:p*=eps if b else 1-eps
    return p

def full_onestep_example(kappa,eps=Q(1,4)):
    # State (a,b,n,h,k), with n a noisy copy of k at stationarity.
    states=bits(5)
    pi={s:Q(1,16)*(eps if s[2]!=s[4] else 1-eps) for s in states}
    assert sum(pi.values())==1
    stationary={s:Q(0) for s in states}
    observed={}
    for s,ps in pi.items():
        a,b,n,h,k=s;q=a^b
        for u in (0,1):
            for z in (0,1):
                y=(z,z^q^u,h)
                for en in bits(3):
                    xp=tuple(v^e for v,e in zip(y,en))
                    pe=prob_noise(en,eps)
                    # Hidden spin expectation kappa*chi(k).
                    for hp in (0,1):
                        ph=(1+kappa*chi((hp,k)))/2
                        prob=ps*Q(1,2)*Q(1,2)*pe*ph
                        sp=xp+(hp,h)
                        stationary[sp]+=prob
                        key=(s[:3],u,xp)
                        observed[key]=observed.get(key,Q(0))+prob
                        # Quotient identity holds pathwise with the same noise.
                        assert (xp[0]^xp[1])==(q^u^en[0]^en[1])
    assert stationary==pi
    return observed, min(pi.values())


def shared_hidden_family(r,m=3,eps=Q(1,4)):
    # Return current observed law and conditional base response signatures.
    law={};pairs={};odd={}
    for x in bits(2*m):
        q=tuple(x[2*i]^x[2*i+1] for i in range(m))
        residual=tuple(x[2*i] for i in range(m))
        # Joint current state and hidden H_t; residual observes previous H.
        joint={}
        for h in (0,1):
            mass=Q(0)
            for g in (0,1):
                pg=Q(1,2)
                ph=r if h==g else 1-r
                likelihood=Q(1)
                for ri in residual:likelihood*=eps if ri!=g else 1-eps
                mass+=pg*ph*likelihood/Q(2**m)
            joint[h]=mass
        px=sum(joint.values());law[x]=px
        for u in (0,1):
            f=q[1:]+(q[0]^(q[1]&q[-1])^u,)
            ys={h:tuple(v for fi in f for v in (h,h^fi)) for h in (0,1)}
            for ij in combinations(range(2*m),2):
                response=sum(joint[h]*chi(tuple(ys[h][i] for i in ij)) for h in (0,1))/px
                assert response in (-1,1)
                pairs[x,u,ij]=response
            odd[x,u]=sum(joint[h]*chi((ys[h][0],)) for h in (0,1))/px
            for i in range(m):assert pairs[x,u,(2*i,2*i+1)]==chi((f[i],))
    assert sum(law.values())==1
    return law,pairs,odd


def main():
    o1,pmin1=full_onestep_example(Q(1,4))
    o2,pmin2=full_onestep_example(Q(3,4))
    assert o1==o2
    lag2=[k*Q(1,2)**2 for k in (Q(1,4),Q(3,4))]
    assert lag2[0]!=lag2[1]
    l1,e1,a1=shared_hidden_family(Q(3,4))
    l2,e2,a2=shared_hidden_family(Q(7,8))
    assert l1==l2 and e1==e2
    witness=next(k for k in a1 if a1[k]!=a2[k])
    # Direct population score validates a Boolean update without Gram regression.
    lam=Q(1,2)**2
    observed_score_moment=Q(0)
    for x,px in l1.items():
        for u in (0,1):
            f=chi((x[2]^x[3],))  # q_0 next = q_1
            observed_parity_mean=lam*e1[x,u,(0,1)]
            observed_score_moment+=px*Q(1,2)*observed_parity_mean*f
    direct_delta=(1-observed_score_moment/lam)/2
    opposite_delta=(1+observed_score_moment/lam)/2
    assert direct_delta==0 and opposite_delta==1
    # Same current residuals, different preceding residuals: non-Markov X.
    def future_residual_mean(previous_bit,r=Q(3,4),eps=Q(1,4),m=3):
        den=Q(0);num=Q(0)
        for g,h in bits(2):
            w=Q(1,2)*(r if h==g else 1-r)
            w*=(eps if previous_bit!=g else 1-eps)**m
            w*=(eps if h!=0 else 1-eps)**m
            den+=w;num+=w*chi((h,))*(2*r-1)*(1-2*eps)
        return num/den
    history_means=[future_residual_mean(v) for v in (0,1)]
    assert history_means[0]!=history_means[1]
    # Exact parity-flip law and conservative finite-path domination factors.
    eps=Q(1,4);rho=sum(prob_noise(e,eps) for e in bits(2) if e[0]^e[1])
    assert rho==2*eps*(1-eps)==Q(3,8)
    R=Q(2);pmin=Q(1,2);delta=Q(1,1000);H=4
    bound=R*delta*sum(pmin**(-(t+1)) for t in range(H))
    assert bound==Q(3,50)
    result={'status':'PASS','exact_stationary_one_step_entries':len(o1),
      'order_two_hidden_parameters':['1/4','3/4'],
      'order_two_stationary_min_mass':str(min(pmin1,pmin2)),
      'residual_lag_two_correlations':[str(x) for x in lag2],
      'growing_family_checked_raw_states':len(l1),
      'exact_conditional_pair_response_entries':len(e1),
      'hidden_persistence_parameters':['3/4','7/8'],
      'odd_query_distinguishing_values':[str(a1[witness]),str(a2[witness])],
      'nonmarkov_same_current_different_history_means':[str(x) for x in history_means],
      'direct_score_mismatch':str(direct_delta),
      'opposite_candidate_score_mismatch':str(opposite_delta),
      'parity_noise_probability':str(rho),
      'example_approx_transfer_bound':str(bound),
      'scope':'Exact Fraction fixtures. Shared hidden family is indistinguishable only under current-state/even-response protocol; order-two fixture matches all stationary one-step readouts, not full histories.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
