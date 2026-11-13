"""Exhaust finite integer allocations of the declared end-to-end timing budget.
This checks arithmetic/schedule semantics, not actual hardware scheduling bounds.
"""
import itertools,json
from pathlib import Path
n=0;worst=0;positive=0
for v in range(700,1201,100):
 for sense,network in itertools.product([0,100],repeat=2):
  normal=v+100+sense+10+network;watch=v+310
  promised=min(normal,watch)+10
  for ds,da,dw,act in itertools.product(range(11),repeat=4):
   if ds+da+dw+act>10:continue
   physical=min(normal+ds+da,watch+dw)+act
   assert physical<=promised
   n+=1;worst=max(worst,physical-min(normal,watch));positive+=min(ds,da,dw,act)>0
# Invalid independent10ms-per-stage budget really can defeat the warm margin.
assert min(1310+10+10,1410+10)+10>1320
out={'integer_allocation_schedule_checks':n,'strictly_positive_all_stage_allocations':positive,'maximum_additional_delay_ms':worst,'assumption':'sum of sample dispatch, acknowledgement dispatch, watchdog scheduling lateness and actuator engagement delays <=10ms, in addition to nominal computation10ms','hardware_timing_measured':False}
p=Path(__file__).with_name('timing_budget_results.json');p.write_text(json.dumps(out,indent=2)+'\n');print(out)
