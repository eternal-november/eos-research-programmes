"""Generic two-type incentive-compatibility LP, checked against exact algebra."""
from itertools import product
from scipy.optimize import linprog

count=0
for v,a,q in product(range(4,13),range(1,5),(0,.2,.35,.5,.65,.8,1)):
    if a>=v: continue
    # Max profit, where utility is net of the receiver's rejection allocation.
    r=linprog([-(1-q)*v,-q*(v-a),1-q,q],
              A_ub=[[0,a,-1,1],[-a,0,1,-1]],b_ub=[0,0],
              bounds=[(0,1),(0,1),(0,None),(0,None)],method='highs')
    assert r.success
    assert abs(-r.fun-max((1-q)*v,v-a))<1e-8
    count+=1
print(count,'generic lottery mechanisms matched the exact pricing bound (numerical LP)')
