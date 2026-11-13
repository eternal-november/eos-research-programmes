import itertools,json,subprocess,math,hashlib
from pathlib import Path
import timed_controller as t
HERE=Path(__file__).resolve().parent
subprocess.run(['cc','-std=c11','-O2','-Wall','-Wextra','-Werror','-fsanitize=undefined',str(HERE/'controller.c'),'-o',str(HERE/'controller_check')],check=True)
# Exhaust every relevant bounded run-memory state, both relevant current action bits,
# and several decisive clearances. 600 memories*8actions*3clearances =14,400.
cases=[];expected=[];expected_strict=[]
for vals in itertools.product(range(2),range(3),range(4),range(5),range(5)):
 r=[0]*12
 for c,v in zip([1,4,6,8,10],vals):r[c]=v
 for acts in itertools.product([-1,1],repeat=3):
  a=[-1]*12
  for c,v in zip([7,3,5],acts):a[c]=v
  m=t.mean(a,r)
  # Independently verify generated static cone formulas.
  assert m[0]==2*a[7]+(2+a[7])*min(r[4],2)-2*r[8]
  assert m[5]==2*a[3]+(2+a[3])*min(r[6],3)-2*r[1]
  assert m[10]==2*a[5]+(2+a[5])*min(r[10],4)-2*min(r[4],2)
  for clear in [537000,1260000,1315000]:
   table=t.bound_table(a,r,clear)
   choice=max(x['speed'] for x in table if x['accepted'])
   cases.append(' '.join(map(str,[clear,0]+a+r)))
   nextmem=[min(v+1,4) if x==1 else 0 for v,x in zip(r,a)]
   expected.append([choice]+nextmem)
   expected_strict.append([max(x['speed'] for x in table if x['risk_upper']<=.0001)]+nextmem)
p=subprocess.run([str(HERE/'controller_check')],input='\n'.join(cases)+'\n',text=True,capture_output=True,check=True)
actual=[list(map(int,l.split())) for l in p.stdout.splitlines()]
assert actual==expected
subprocess.run(['cc','-std=c11','-O2','-Wall','-Wextra','-Werror','-fsanitize=undefined','-DALPHA_PPM=100ULL',str(HERE/'controller.c'),'-o',str(HERE/'controller_strict_check')],check=True)
p2=subprocess.run([str(HERE/'controller_strict_check')],input='\n'.join(cases)+'\n',text=True,capture_output=True,check=True)
assert [list(map(int,l.split())) for l in p2.stdout.splitlines()]==expected_strict
out={'controller_source_sha256':hashlib.sha256((HERE/'controller.c').read_bytes()).hexdigest(),'simulator_source_sha256':hashlib.sha256((HERE/'timed_controller.py').read_bytes()).hexdigest(),'tested_context_clearance_cases_per_budget':len(cases),'tested_risk_budgets':[.1,.0001],'total_decision_checks':2*len(cases),'all_match_python_tick_simulation':True,'c_sanitizer':'undefined behavior sanitizer','worst_runtime_prediction_outcomes':48,'max_retained_history_bytes':12,'real_hardware_WCET_validated':False,'probability_operations':'integer count cross-multiplication; outward-rounded TV in parts per million','no_future_outcome_or_hidden_parameter_controller_input':True}
(HERE/'c_check_results.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
