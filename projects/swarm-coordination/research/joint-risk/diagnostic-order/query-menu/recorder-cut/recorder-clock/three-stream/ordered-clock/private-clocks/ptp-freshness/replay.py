#!/usr/bin/env python3
"""Check whether a selected LinuxPTP report implies a fresh offset update."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


def exact(p,digest):
    raw=Path(p).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==digest
    return raw.decode()


def function(code,header):
    start=code.index(header)
    return code[start:code.index('\n}\n',start)+2]


def main(clock,proc):
    c=exact(clock,'7bacb099d56657691619ceb711ea7a07ed803085')
    p=exact(proc,'a871049602a40d1c02da0416de4f8e295df89508')
    h='enum servo_state clock_synchronize('
    i=c.index(h)
    prefix=c[i:c.index('\n\tif (clock_utc_correct(c, ingress))',i)]
    report=c[c.index('\tcase MID_TIME_STATUS_NP:'):c.index('\tcase MID_GRANDMASTER_SETTINGS_NP:')]
    update=function(p,'int tsproc_update_offset(')
    down=function(p,'void tsproc_down_ts(')
    code=Path(__file__).with_name('fixture.c').read_text()
    for key,val in [("INSERT_UPDATE",update),("INSERT_DOWN",down),("INSERT_PRE",prefix),
                    ("INSERT_TLV",report)]:
        code=code.replace(key,val)
    with tempfile.TemporaryDirectory() as directory:
        path=Path(directory)
        (path/'run.c').write_text(code)
        subprocess.run(['cc','-std=c11','-o',str(path/'run'),str(path/'run.c')],check=True)
        subprocess.run([str(path/'run')],check=True)


if __name__=='__main__':
    main(*sys.argv[1:])
