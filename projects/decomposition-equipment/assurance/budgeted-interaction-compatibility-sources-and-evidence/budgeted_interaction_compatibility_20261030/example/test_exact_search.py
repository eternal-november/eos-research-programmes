import unittest
from exact_search import ExactSearch, Step, WIN, LOSE, UNKNOWN

class Toy:
    def encode_state(self,s): return list(s)
    def encode_action(self,a): return a
    def encode_observation(self,o): return o
    def terminal(self,s):
        t,good=s
        return (WIN if good else LOSE, 'horizon') if t == 2 else None
    def actions(self,s): return ['unsafe','split','sure']
    def transition(self,s,a):
        t,good=s
        if a=='unsafe': return Step(unsafe={'world':0})
        if a=='split': return Step(outcomes=((0,(t+1,False)),(1,(t+1,True))))
        return Step(outcomes=((0,(t+1,good)),))

class Test(unittest.TestCase):
    def test_win(self):
        r=ExactSearch(Toy()).solve((0,True));self.assertEqual(r['status'],WIN)
        self.assertEqual(r['certificate'][r['root']]['action'],'sure')
    def test_lose(self):
        r=ExactSearch(Toy()).solve((0,False));self.assertEqual(r['status'],LOSE)
        self.assertEqual(len(r['certificate'][r['root']]['actions']),3)
    def test_unknown_is_not_lose(self):
        r=ExactSearch(Toy(),max_nodes=0).solve((0,True))
        self.assertEqual(r['status'],UNKNOWN);self.assertFalse(r['certificate'])
    def test_boundary_before_limit(self):
        r=ExactSearch(Toy(),max_nodes=0).solve((2,True));self.assertEqual(r['status'],WIN)

if __name__=='__main__': unittest.main()
