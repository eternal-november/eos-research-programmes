#!/usr/bin/env python3
"""Compose pinned RMF door source/status functions with inert simulator and ROS types."""
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile


def exact(name,expected):
    raw=Path(name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==expected
    return raw.decode()


def body(source,marker):
    m=re.search(marker,source,flags=re.M)
    assert m
    left=source.index('{',m.end())
    dep=1
    right=left+1
    while dep:
        dep+=(source[right]=='{')-(source[right]=='}')
        right+=1
    return source[m.start():right]


def main(sim,phase,session,utils):
    u=exact(utils,'a84cf6fcbb95b2fda96e580c6e248cab33aa46c1')
    d=exact(sim,'3972e4308f44ad3cd90a0e139484f9d2d6813b68')
    p=exact(phase,'c57241738d140d45a958457a69ae2c563e6e4988')
    s=exact(session,'691945ac652bfc1a8ad8ebea403a7de11ee8d2c8')
    assert 'transport->door_state().combine_latest(' in p
    assert 'me->_update_status(std::get<0>(v), std::get<1>(v));' in p
    cases={key:body(d,pattern) for key,pattern in (
        ("JOINT_SRC",r"^  Entity get_joint_entity\("),
        ("WITHIN_SRC",r"^  bool is_joint_at_position\("),
        ("MODE_SRC",r"^  DoorModeCmp get_current_mode\("),
        ("TARGET_SRC",r"^  double calculate_target_velocity\("),
        ("COMMAND_SRC",r"^  void command_door\("),
        ("PUBLISH_SRC",r"^  void publish_state\("))}
    cases['UPDATE_SRC']=body(p,r"^void DoorOpen::ActivePhase::_update_status\(")
    cases['SESSION_SRC']=body(s,r"^bool supervisor_has_session\(")
    code=Path(__file__).with_name("door_effect.cc.in").read_text()
    for k,v in cases.items():
        assert code.count(k)==1
        code=code.replace(k,v)
    with tempfile.TemporaryDirectory() as folder:
        d=Path(folder)
        (d/"replay.cc").write_text(code)
        (d/"utils.hpp").write_text(u)
        launch=['c++','-std=c++20','-Wall','-Wextra','-o',str(d/'test'),str(d/'replay.cc')]
        subprocess.run(launch,check=True)
        r=subprocess.run([str(d/"test")],check=True,capture_output=True,text=True)
        assert not r.stderr
        print(r.stdout,end='')


if __name__=="__main__":
    main(*sys.argv[1:])
