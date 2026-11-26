#!/usr/bin/env python3
"""Use the calibration-cut harness with actual pinned edge/trajectory classes."""
from pathlib import Path
import hashlib,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
UP=Path(sys.argv[1])
def src(f,h):
    b=(UP/f).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==h,f
    return b.decode()
def ns(s):
    return s[s.index('namespace vda5050_core {'):].split('#endif')[0]
def method(s,name):
    i=s.rindex('\n',0,s.index('::'+name+'('))+1
    return s[i:s.index('\n}',i)+2]
tfh=src('transformation.hpp','0a8f4291a23db940aaded403e3446b7354ef8281')
nrh=src('node_request.hpp','53ffb986457fc33a01c73df92af437a344061e24')
tfc=src('transformation.cpp','b310a2c1a78a87127e60ea959bab633f77d9e608')
nrc=src('node_request.cpp','04a55670513c803ce4b57c28d7990ab194ceaba9')
erc=src('edge_request.cpp','db918bc4dd917752401e6055adb2b3b01b7693b5')
erh=src('edge_request.hpp','5c821571c4f4647f928ee63c5445680a98473a98')
tph=src('trajectory.hpp','8e54736a1f8fcf234e37c3351e0c0bde4a34732f')
cph=src('control_point.hpp','3a495c45af3c6d25c72914f48c4a7595495fb770')
sm=src('state_manager.cpp','1d437d3cb5081bd661089be3f9f6e17c1ee99dc1')
ad=src('adapter.cpp','76e71ef7b8e25bb794f258cf5e290004b0fae2ba')
stubs=(HERE.parent/'fixture.hpp').read_text()
def change(p,q,s):
    assert s.count(p)==1,p
    return s.replace(p,q)
stubs=change('struct Order {','''struct Edge {
  std::string edge_id;
  uint32_t sequence_id;
  std::optional<Trajectory> trajectory;
  std::optional<double> max_speed,min_height,max_height,max_rotation_speed,length;
  std::optional<bool> rotation_allowed;
};
struct Order {''',stubs)
stubs=change('std::vector<int> edges;', 'std::vector<Edge> edges;',stubs)
stubs=change('void edge_traversed(int)', 'void edge_traversed(const types::Edge&)',stubs)
stubs=change('struct EdgeRequest { static EdgeRequest from_edge(int) {assert(false);return {};} };',
    '}\n}\n'+ns(erh)+'\nnamespace vda5050_core::client::adapter {',stubs)
i=stubs.rindex('\n}\n}')
stubs=stubs[:i]+'\n}\n'
with tempfile.TemporaryDirectory() as d:
    s='\n'.join(['#include <cmath>\n#include <numbers>\n#include <cstdint>\n#include <optional>\n#include <string>\n#include <vector>',
        ns(tfh),ns(tfc),ns(cph),ns(tph),stubs,ns(nrh),ns(nrc),ns(erc),
        'namespace vda5050_core::client::adapter {',
        *(method(sm,n) for n in ('set_position','initialize_position','set_transformation','transformation','state')),
        method(ad,'process_navigation'),'}',(HERE/'trace.inc').read_text()])
    p=Path(d)
    (p/'check.cc').write_text(s)
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror','-o',p/'check',p/'check.cc'],check=True)
    subprocess.run([p/'check'],check=True)
