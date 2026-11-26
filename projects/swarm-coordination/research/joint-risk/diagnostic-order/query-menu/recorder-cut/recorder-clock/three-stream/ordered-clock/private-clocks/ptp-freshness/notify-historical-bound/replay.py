#!/usr/bin/env python3
"""Pinned LinuxPTP synchronization and notification, inert clock/transport."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile


def exact(path,sha):
    raw=Path(path).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==sha
    return raw.decode()


def fun(src,mark):
    i=src.index(mark)
    return src[i:src.index('\n}\n',i)+2]


def main(clock,tsproc):
    c=exact(clock,'7bacb099d56657691619ceb711ea7a07ed803085')
    p=exact(tsproc,'a871049602a40d1c02da0416de4f8e295df89508')
    code=Path(__file__).with_name('fixture.c').read_text()
    for key,val in [
        ("INSERT_UPDATE",fun(p,'int tsproc_update_offset(')),
        ("INSERT_DOWN",fun(p,'void tsproc_down_ts(')),
        ("INSERT_RESET",fun(p,'void tsproc_reset(')),
        ("INSERT_SYNC",fun(c,'enum servo_state clock_synchronize(')),
        ("INSERT_NOTIFY",fun(c,'void clock_notify_event(')),
        ("INSERT_STEPWINDOW",fun(c,'static void clock_step_window(')),
        ("INSERT_TLV",c[c.index('\tcase MID_TIME_STATUS_NP:'):c.index('\tcase MID_GRANDMASTER_SETTINGS_NP:')])
    ]:
        code=code.replace(key,val)
    with tempfile.TemporaryDirectory() as directory:
        d=Path(directory)
        (d/'run.c').write_text(code)
        subprocess.run(['cc','-std=c11','-Wall','-Wextra','-o',str(d/'run'),str(d/'run.c')],check=True)
        subprocess.run([str(d/'run')],check=True)


if __name__=='__main__':
    main(*sys.argv[1:])
