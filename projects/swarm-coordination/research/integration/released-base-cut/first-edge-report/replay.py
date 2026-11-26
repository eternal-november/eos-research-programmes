#!/usr/bin/env python3
"""Extract and compile selected pinned bodies with inert local stand-ins."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


def pin(path, sha):
    raw=Path(path).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==sha
    return raw.decode()


def method(s,name):
    start=s.index(name)
    end=s.index('\n}\n',start)+len('\n}\n')
    return s[start:end]


def main(validator, manager, adapter, request):
    v=pin(validator,'f8e427852e3afaf357fae7dc3f96dbbe78bc2c9f')
    m=pin(manager,'1d437d3cb5081bd661089be3f9f6e17c1ee99dc1')
    a=pin(adapter,'76e71ef7b8e25bb794f258cf5e290004b0fae2ba')
    e=pin(request,'db918bc4dd917752401e6055adb2b3b01b7693b5')
    # The inert request constructor retains the same two used fields.
    assert 'edge.edge_id, edge.sequence_id, edge.trajectory' in e
    p=Path(__file__).resolve().parent
    parts=[(p/'fixture.hpp').read_text(),v[v.index('namespace vda5050_core::validation {'):],
        'namespace vda5050_core::client::adapter {',
        method(m,'void StateManager::set_order('),
        method(a,'void Adapter::Implementation::process_navigation('),'}',
        (p/'tests.cc').read_text()]
    with tempfile.TemporaryDirectory() as d:
        q=Path(d)
        (q/'run.cc').write_text('\n'.join(parts))
        subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-pedantic','-o',str(q/'run'),str(q/'run.cc')],check=True)
        subprocess.run([str(q/'run')],check=True)


if __name__=='__main__':
    main(*sys.argv[1:])
