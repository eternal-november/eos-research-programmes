import copy,unittest
from exact_search import ExactSearch
from test_exact_search import Toy
from check_certificate import check_certificate
class Test(unittest.TestCase):
    def test_missing_outcome_rejected(self):
        r=ExactSearch(Toy()).solve((0,True));r['certificate'][r['root']]['outcomes']=[]
        with self.assertRaises(AssertionError):check_certificate(Toy(),(0,True),r)
    def test_missing_losing_action_rejected(self):
        r=ExactSearch(Toy()).solve((0,False));r['certificate'][r['root']]['actions'].pop()
        with self.assertRaises(AssertionError):check_certificate(Toy(),(0,False),r)
    def test_successor_mismatch_rejected(self):
        r=ExactSearch(Toy()).solve((0,True));r['certificate'][r['root']]['outcomes'][0]['next']='bad'
        with self.assertRaises(AssertionError):check_certificate(Toy(),(0,True),r)
    def test_state_mutation_rejected(self):
        r=ExactSearch(Toy()).solve((0,False));r['certificate'][r['root']]['state'][0]=999
        with self.assertRaises(AssertionError):check_certificate(Toy(),(0,False),r)
if __name__=='__main__':unittest.main()
