import unittest,random
from itertools import product
from ladder_model import LadderInference,LadderModel,Job

class TestLadder(unittest.TestCase):
    def compare(self,n,domains,previous):
        inf=LadderInference(n)
        worlds=list(inf.complete_worlds(domains))
        support=inf.support(domains)
        if not worlds:self.assertIsNone(support);return
        expected=tuple(inf.mask(i,{w[i] for w in worlds}) for i in range(n))
        self.assertEqual(support,expected)
        observations={tuple(0 if p<0 else previous[p] for p in w) for w in worlds}
        actual=dict(inf.outcomes(domains,previous))
        self.assertEqual(set(actual),observations)
        for o,d in actual.items():
            branch=[w for w in worlds if tuple(0 if p<0 else previous[p] for p in w)==o]
            target=tuple(inf.mask(i,{w[i] for w in branch}) for i in range(n))
            self.assertEqual(d,target)
    def test_all_n4_domains(self):
        inf=LadderInference(4)
        for domains in product(range(1,8),repeat=4):
            worlds=list(inf.complete_worlds(domains));s=inf.support(domains)
            expected=None if not worlds else tuple(inf.mask(i,{w[i] for w in worlds}) for i in range(4))
            self.assertEqual(s,expected)
    def test_joint_outcomes_random(self):
        rng=random.Random(123456)
        for n in (4,6,8):
            inf=LadderInference(n)
            for _ in range(60):
                domains=tuple(rng.randrange(1,1<<len(c)) for c in inf.choices)
                previous=tuple(rng.randrange(3) for i in range(n))
                self.compare(n,domains,previous)
    def test_current_controls_do_not_reveal_current_outgoing(self):
        m=LadderModel(4,[Job(2,3,((0,1),(1,0)))],2,5)
        s=m.initial()
        for a in m.actions(s):
            st=m.transition(s,a)
            self.assertEqual(len(st.outcomes),1)
            self.assertEqual(st.outcomes[0][1].domains,s.domains)

if __name__=='__main__':unittest.main()
