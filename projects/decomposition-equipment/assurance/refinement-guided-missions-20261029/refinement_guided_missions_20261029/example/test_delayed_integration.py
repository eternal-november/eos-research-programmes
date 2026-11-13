"""Small hand-fixture regression, separate from fixed outcome workload."""
import unittest
import numpy as np
from delayed_missions import Plant, Knowledge, plan, check_schedule, execute_binary
class IntegrationTests(unittest.TestCase):
 def test_safe_identification_and_positive_service(self):
  n,L,s=3,2,3
  G=np.zeros((n,L+1,n),dtype=int)
  G[0,0,0]=4;G[1,1,1]=3;G[2,2,2]=2
  plant=Plant(G,L,1);knowledge=Knowledge(n,L,s,'cached_column')
  for j in range(n):knowledge.probe(j,plant)
  self.assertTrue(np.array_equal(knowledge.G,G))
  spec={'deadline':10,'jobs':[{'release':0,'due':10,'stages':[{'duration':1,'modes':[(0,),(1,)]},{'duration':1,'modes':[(1,),(2,)]}]}]}
  schedule,info=plan(spec,n,L,2,0,G,set())
  self.assertIsNotNone(schedule,info)
  self.assertTrue(check_schedule(schedule,spec,n,L,2)[0])
  self.assertTrue(knowledge.certify(schedule['U'])[0])
  A,B=execute_binary(plant,schedule['U'],'service',4)
  knowledge.observe(A,B,'service')
  self.assertTrue(all(t['worst_envelope_safe'] for t in plant.trace))
  self.assertEqual(knowledge.stats['column_probes'],n)
if __name__=='__main__':unittest.main()
