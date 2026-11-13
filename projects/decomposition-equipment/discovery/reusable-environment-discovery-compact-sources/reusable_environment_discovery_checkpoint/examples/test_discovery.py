"""Focused regression tests; no simulator truth passed to discovery routines."""
import itertools, unittest
from fractions import Fraction
import numpy as np
from check_growing_memory_environment import (L,true_models,evaluate_terms,quotient_for_channel,
    scalar_value,recover_groups,split_distance_triple,discover_mean,support_validate,estimate_kernels)

class DiscoveryTests(unittest.TestCase):
    def test_triple_marginals_do_not_determine_joint(self):
        rho=.37
        rows=list(itertools.product((-1,1),repeat=3))
        p=np.array([(1+rho*np.prod(z))/8 for z in rows])
        for pair in itertools.combinations(range(3),2):
            self.assertAlmostEqual(sum(q*z[pair[0]]*z[pair[1]] for q,z in zip(p,rows)),0)
        self.assertAlmostEqual(split_distance_triple(0,0,rho),rho/2)
        self.assertAlmostEqual(sum(q for q,z in zip(p,rows) if np.prod(z)==1),.685)

    def test_polynomial_support_bound_attained(self):
        for d in range(1,6):
            vals=[int(all(x==1 for x in z)) for z in itertools.product((-1,1),repeat=d)]
            self.assertEqual(sum(v!=0 for v in vals),1)
            self.assertEqual(sum(v!=0 for v in vals)/len(vals),2**(-d))

    def test_quotient_counts_and_updates(self):
        n=12; models,_=true_models(n,123)
        tables=[quotient_for_channel(models,n,j) for j in range(n)]
        self.assertEqual(set(t['selected_order'] for t in tables),{1,2,3,4})
        for t in tables:
            self.assertEqual(t['quotient_states'],t['selected_order']+1)
            words=list(itertools.product((-1,1),repeat=L));ix={w:i for i,w in enumerate(words)}
            for i,w in enumerate(words):
                for a in (-1,1):
                    self.assertEqual(t['transition_minus_plus'][t['partition'][i]][int(a==1)],
                                     t['partition'][ix[w[1:]+(a,)]])

    def test_wrong_response_fails_independent_support_validation(self):
        n=12; models,_=true_models(n,123)
        rng=np.random.default_rng(19)
        actions=rng.choice(np.array([-1,1],dtype=np.int8),size=(L+7000,n))
        y=evaluate_terms(actions,models)+rng.choice([-1,1],size=(7000,n))
        wrong=[dict(m) for m in models];wrong[0]=dict(wrong[0]);wrong[0]['intercept']=7
        _,cert=support_validate(actions,y,wrong,1000,6000)
        self.assertFalse(cert['passed'])
        self.assertGreater(cert['per_output_violations'][0],0)

    def test_exact_probability_certificate_rounding(self):
        z=np.array(list(itertools.product((-1,1),repeat=3))*16)
        _,cert=estimate_kernels(z,[[0,1,2]])
        D=cert['gamma_shape_dimension'];s=cert['ceil_sqrt_12D']
        self.assertGreaterEqual(s*s,12*D)
        self.assertLess((s-1)*(s-1),12*D)
        x=cert['integer_threshold_N_times_KL'];self.assertEqual(x,D+s+6)
        val=sum((Fraction(6)**j)/__import__('math').factorial(j) for j in range(cert['exact_rational_exp6_lower_bound_terms']))
        self.assertGreater(val,400)
        for H,bound in cert['trajectory_TV_bounds'].items():
            if bound<1:
                self.assertGreaterEqual(Fraction(str(bound))**2,Fraction(int(H)*x,2*len(z)))

    def test_raw_evaluator_time_index(self):
        n=12;models,_=true_models(n,777)
        a=np.random.default_rng(12).choice([-1,1],size=(L+20,n))
        v=evaluate_terms(a,models)
        for t in range(20):
            self.assertEqual(v[t].tolist(),[scalar_value(m,a[t:t+L+1],n) for m in models])

if __name__=='__main__': unittest.main()
