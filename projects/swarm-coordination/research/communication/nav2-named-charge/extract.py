from pathlib import Path
from hashlib import sha1
import re
pins={'dock_src.cpp':'3371e7136cfd84f5f8c4d4eb882bc53abccd7c25','server_src.cpp':'50f5acc18a4312c7c884053d38b26acc0d44b495','db_src.cpp':'e6c1f644b24281214ec7df2a18093f6214f46191','DockRobot.action':'8acf7b8b3a2a8fba159268013d4e4fd49dd63b43'}
ss={}
for f,g in pins.items():
 b=Path(f).read_bytes()
 assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==g
 ss[f]=b.decode()
s=ss['dock_src.cpp']
server=ss['server_src.cpp']
db=ss['db_src.cpp']
def get(start):
 a=s.index('bool SimpleChargingDock::'+start+'()');b=s.index('\n}',a)+2
 return s[a:b]
p=re.search(r'        (is_charging_ = state->current > charging_threshold_;)',s).group(1)
guard=re.search(r'    if \((dock->plugin->isCharger\(\) && \(dock->plugin->isDocked\(\) \|\| dock->plugin->isCharging\(\)\))\) \{',server).group(1)
assert server.index(guard)<server.index('dock->getStagingPose()')
assert 'dock_instance->plugin = dock_plugin;' in db and 'findDockPlugin(dock_instance->type)' in db
assert 'dock_plugins_.insert({docks_plugins[i], dock});' in db
assert 'bool success true' in ss['DockRobot.action']
assert 'dock_id' not in ss['DockRobot.action'].split('---')[1]
notice=s[:s.index('#include')]
Path('source.inc').write_text(notice+'\n\n'.join(get(k) for k in ['isDocked','isCharging','disableCharging','hasStoppedCharging'])+'\n')
Path('branches.inc').write_text(notice+'void SimpleChargingDock::battery_sample(double current) {\n struct State {double current;} sample{current}; auto state=&sample;\n '+p+'\n}\n'
  +'bool existing_dock_path(Dock* dock) { return '+guard+'; }\n')
