#!/usr/bin/env python3
"""Execute the pinned shared wind force application with a serial component fixture."""
import hashlib, subprocess, sys, tempfile
from pathlib import Path
here=Path(__file__).resolve().parent
b=Path(sys.argv[1]).read_bytes()
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()=='f978553c334908420914b58b9915f161bc2ac6b3'
s=b.decode()
i=s.index('void WindEffectsPrivate::ApplyWindForce(')
body=s[i:s.index('\n}',i)+2]
with tempfile.TemporaryDirectory() as d:
    d=Path(d); f=d/'wind.cc'
    f.write_text((here/'fixture.inc').read_text()+body+(here/'traces.inc').read_text())
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror',f,'-o',d/'wind'],check=True)
    subprocess.run([d/'wind'],check=True)
