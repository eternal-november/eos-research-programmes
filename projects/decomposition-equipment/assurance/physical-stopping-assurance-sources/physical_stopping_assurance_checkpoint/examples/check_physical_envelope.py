from fractions import Fraction
from pathlib import Path
import json
import timed_controller as t
count=0;gap=Fraction()
for v in t.SPEEDS[1:]:
 for sensor_y in [-3,-1,3]:
  for network_y in [-3,-1,3]:
   for brake_y in range(-4,6):
    y=(sensor_y,network_y,brake_y);s,n,b=t.physical(y)
    bound=t.simulate(v,y,10**9)['stop_um']
    delay=min(100+s+10+n,310)+10
    exact=Fraction(v*v,2)+v*delay+Fraction(500*v*v,b)
    assert bound>=exact
    gap=max(gap,bound-exact);count+=1
out={'continuous_constant_deceleration_comparisons':count,'all_tick_stopping_distances_upper_bound_continuous_motion':True,'maximum_rounding_excess_um':str(gap),'collision_field_semantics':'conservative protected-boundary envelope violation; exact collision only when actual trajectory attains the envelope'}
Path(__file__).with_name('physical_envelope_results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
