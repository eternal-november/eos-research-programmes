#!/usr/bin/env python3
"""Run pinned Open-RMF door supervisor methods with inert message transport."""
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile


def extract(source,marker):
    p=source.index(marker)
    q=source.index('\n}\n',p)+2
    return source[p:q]


def main(path):
    src=Path(path).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(src)).encode()+b'\0'+src).hexdigest()=='5b5f149af7b0702eed6fefad5fc9ee9ae1c7311f'
    s=src.decode()
    code=Path(__file__).with_name("fixture.cc").read_text()
    names=("_process_open_request","_process_close_request","_send_open_request",
           "_send_close_request","_publish_heartbeat")
    glue='\n'.join(extract(s,"void Node::"+m+"(") for m in names)
    assert code.count("METHODS_SRC")==1
    code=code.replace("METHODS_SRC",glue)
    with tempfile.TemporaryDirectory() as folder:
        d=Path(folder)
        (d/"run.cc").write_text(code)
        subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-o',str(d/'run'),str(d/'run.cc')],check=True)
        subprocess.run([str(d/'run')],check=True)


if __name__=="__main__":
    main(*sys.argv[1:])
