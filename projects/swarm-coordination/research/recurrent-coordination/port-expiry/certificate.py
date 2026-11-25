"""Generate a finite-state potential for the exact tight phase-limited pair."""
import json
from fractions import Fraction
from model import automaton,upper_cycle_bound, equality_witness
A=(1,3,4,1);B=(1,1,6,1)
s,e=automaton(A,B)
p,_=upper_cycle_bound(s,e,3,2,Fraction(2))
w=equality_witness(s,e,3,2,Fraction(2))
assert w
cert={'parameters':(A,B), 'weights':[3,2], 'cap':2,
      'potential':[[x,y] for x,y in zip(s,p)],
      'witness':['A.BAA.BA', 'BA.BAAB.ABA.BAAB.A']}
with open('potential.json','w') as f:
    f.write(json.dumps(cert,separators=(',',':'),sort_keys=True)+'\n')
print(len(s),len(e),w)
