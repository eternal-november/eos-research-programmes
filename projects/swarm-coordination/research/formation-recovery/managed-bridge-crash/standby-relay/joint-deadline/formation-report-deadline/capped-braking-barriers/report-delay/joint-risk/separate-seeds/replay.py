#!/usr/bin/env python3
"""Independent exact decoding games on an even probability grid."""
from fractions import Fraction as Q
from itertools import product
from math import prod
import json


def worst_risk(pa,pb,d,ps):
    lo,hi=max(0,d-pb),min(d,pa)
    X,Y=prod(ps),prod(1-p for p in ps)
    return d-min(q*X+(d-q)*Y for q in (lo,hi))


def replay():
    cases=candidates=0
    for g in range(1,6):
        den=4
        scale=den**g
        products=[(prod(p),prod(den-x for x in p))
                  for p in product(range(den+1),repeat=g)]
        for pa,d in product(range(11),repeat=2):
            pb=10-pa
            l,u=max(0,d-pb),min(d,pa)
            best=max(min(l*x+(d-l)*y,u*x+(d-u)*y) for x,y in products)
            assert Q(d*scale-best,scale)==min(pa,pb,Q(d*(2**g-1),2**g))
            cases+=1
            candidates+=len(products)
    assert worst_risk(Q(1,2),Q(1,2),Q(1,10),[Q(1,2)]*4)==Q(3,32)
    assert worst_risk(Q(1,2),Q(1,2),Q(1,10),[Q(1,2)])==Q(1,20)
    assert worst_risk(Q(1,20),Q(19,20),Q(1,2),[Q(0)]*4)==Q(1,20)
    return dict(prior_erasure_group_games=cases,
                exact_strategy_evaluations=candidates,
                one_seed_equal_priors="1/20",
                four_seeds_equal_priors="3/32")


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
