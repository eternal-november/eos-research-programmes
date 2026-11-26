#!/usr/bin/env python3
"""Run pinned velocity cache assignments and selected downstream source bodies."""
from pathlib import Path
import hashlib, sys, subprocess, tempfile
here=Path(__file__).resolve().parent
up=Path(sys.argv[1]).resolve()
base=Path(sys.argv[2]).resolve() if len(sys.argv)>2 else here.parent.parent
def pull(s,begin,end):
    i=s.index(begin)
    return s[i:s.index(end,i)+len(end)]
raw=(up/'VelocityControl.cc').read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='7af66e743b17415aba8ff3bf60567e8682541ab8'
s=raw.decode()
assert 'this->dataPtr->UpdateVelocity(_info, _ecm);' in s
driver=(here/'cache.inc').read_text().replace('/*POST_UPDATE_BODY*/',
    pull(s,'void VelocityControlPrivate::UpdateVelocity(', '\n}')).replace('/*MESSAGE_BODY*/',
    pull(s,'void VelocityControlPrivate::OnCmdVel(', '\n}'))
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    for f in ('fixture.inc','replay.py'):
        (d/f).write_bytes((base/f).read_bytes())
    child=d/'dual-writer';child.mkdir()
    (child/'replay.py').write_bytes((base/'dual-writer'/'replay.py').read_bytes())
    (child/'order.inc').write_text(driver)
    subprocess.run([sys.executable,'-B',child/'replay.py',up],check=True)
