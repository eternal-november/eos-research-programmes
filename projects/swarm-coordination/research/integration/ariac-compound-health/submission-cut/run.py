import re
from pathlib import Path
from hashlib import sha1
from tempfile import TemporaryDirectory
from subprocess import run
r=Path(__file__).resolve().parent
b=(r/'upstream.cpp').read_bytes()
assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()=='4b6bc2cea406d4813145d9f565318a4ebe345be8'
s=b.decode()
def cut(name):
    m=re.search(r'^    (?:void|bool)\s+TaskManagerPlugin::'+name+r'\(',s,re.M)
    assert m is not None,name
    return s[m.start():s.index('\n    }',m.end())+6]
site=s[s.index('void TaskManagerPlugin::OnUpdate()'):]
src_order=['ProcessOrdersToAnnounce();','ProcessChallengesToAnnounce();',
           'ProcessInProgressSensorBlackouts();','ProcessInProgressRobotMalfunctions();','UpdateSensorsHealth();']
assert [site.index(i) for i in src_order]==sorted(site.index(i) for i in src_order)
for parent,children in [
    ('ProcessOrdersToAnnounce',['ProcessOnSubmissionOrders']),
    ('ProcessChallengesToAnnounce',['ProcessOnSubmissionSensorBlackouts','ProcessOnSubmissionRobotMalfunctions'])]:
    p=cut(parent)
    assert all(c+'();' in p for c in children)
    assert [p.index(c+'();') for c in children]==sorted(p.index(c+'();') for c in children)
sel=[cut(x) for x in ('SetRobotsHealth','SetSensorsHealth','ProcessOnSubmissionOrders',
    'ProcessOnSubmissionSensorBlackouts','ProcessOnSubmissionRobotMalfunctions','SubmitOrderServiceCallback')]
with TemporaryDirectory() as tmp:
    p=Path(tmp)
    (p/'selected.inc').write_text('\n'.join(sel))
    (p/'replay.cpp').write_bytes((r/'replay.cpp').read_bytes())
    run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-Wno-unused-variable','-Wno-unused-but-set-variable','replay.cpp','-o','replay'],cwd=p,check=True)
    run([p/'replay'],cwd=p,check=True)
