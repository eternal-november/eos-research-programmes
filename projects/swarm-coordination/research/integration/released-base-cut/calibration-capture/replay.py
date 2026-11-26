#!/usr/bin/env python3
"""Compile byte-pinned, unchanged method bodies with a serial inert adapter harness."""
from pathlib import Path
import hashlib,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
UP=Path(sys.argv[1])
def src(f,h):
    b=(UP/f).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==h,f
    return b.decode()
tfh=src('transformation.hpp','0a8f4291a23db940aaded403e3446b7354ef8281')
nrh=src('node_request.hpp','53ffb986457fc33a01c73df92af437a344061e24')
tfc=src('transformation.cpp','b310a2c1a78a87127e60ea959bab633f77d9e608')
nrc=src('node_request.cpp','04a55670513c803ce4b57c28d7990ab194ceaba9')
sm=src('state_manager.cpp','1d437d3cb5081bd661089be3f9f6e17c1ee99dc1')
ad=src('adapter.cpp','76e71ef7b8e25bb794f258cf5e290004b0fae2ba')
test=src('test_adapter_navigation.cpp','17e390b44b22c103f44cc9058f79351a6bc38f98')
assert 'TransformsCoordinatesUsingSetTransform' in test
def ns(s):
    return s[s.index('namespace vda5050_core {'):]
def method(s,name):
    # Containing definition begins at a top-level line, ends at unindented brace.
    i=s.rindex('\n',0,s.index('::'+name+'('))+1
    return s[i:s.index('\n}',i)+2]
with tempfile.TemporaryDirectory() as d:
    s='\n'.join(['#include <cmath>\n#include <cstdint>\n#include <optional>\n#include <string>',
        ns(tfh).split('#endif')[0],ns(tfc),(HERE/'fixture.hpp').read_text(),
        ns(nrh).split('#endif')[0],ns(nrc),
        'namespace vda5050_core::client::adapter {',
        *(method(sm,n) for n in ('set_position','initialize_position','set_transformation','transformation','state')),
        method(ad,'process_navigation'),'}',(HERE/'trace.inc').read_text()])
    p=Path(d)
    (p/'check.cc').write_text(s)
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror','-o',p/'check',p/'check.cc'],check=True)
    subprocess.run([p/'check'],check=True)
