#!/usr/bin/env python3
"""Compile unchanged Source/Scan methods against an explicit transform provider."""
import hashlib,subprocess,tempfile,sys
from pathlib import Path
base=Path(sys.argv[1]);here=Path(__file__).resolve().parent
def src(n,sha):
    x=(base/n).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(x)).encode()+b'\0'+x).hexdigest()==sha,n
    return x.decode()
def pull(s,key):
    i=s.index(key)
    return s[i:s.index('\n}',i)+2]
s=src('source.cpp','b0c387754822aa4b880f14187643d9221aa6e32d')
a=src('scan.cpp','bd1f5ae5620a852543e9ec83e8651def087e205d')
t=src('tf_manager.hpp','efd345c685b9f8b156f06cc9863afe28415df4ec')
assert 'target_frame, target_time, source_frame, source_time, fixed_frame,' in t
with tempfile.TemporaryDirectory() as d:
    p=Path(d)
    (p/'run.cc').write_text('\n'.join([(here/'harness.inc').read_text(),
        'namespace nav2_collision_monitor {',
        pull(s,'bool Source::sourceValid('),pull(s,'bool Source::getTransform('),
        pull(a,'bool Scan::getSourceData('),'}',(here/'test.inc').read_text()]))
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror','-o',p/'run',p/'run.cc'],check=True)
    subprocess.run([p/'run'],check=True)
