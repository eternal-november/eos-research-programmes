#!/usr/bin/env python3
"""Extract native request, local marker, and supervisor bodies; run a lifetime model."""
import hashlib
from pathlib import Path
import re
import subprocess as sp
import sys
import tempfile

HERE=Path(__file__).resolve().parent
PINS={"Supervisor.cc":"5b5f149af7b0702eed6fefad5fc9ee9ae1c7311f",
      "DoorClose.cc":"6a8552737b3f3a080e16ddc8730a233671320f23",
      "RobotContext.cc":"1c342a1cf0887be952f264e695cdb2fc1b698be9",
      "gate_receipt.hpp":"9b24ee7a34f069c4c787e20fd92dad74da4d7597"}
def read(p):
    b=p.read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==PINS[p.name],p
    return b.decode()
def body(s,needle):
    loc=s.index(needle)
    start=s.index("{",loc)+1
    depth=1
    for i,ch in enumerate(s[start:],start):
        depth+=(ch=="{")-(ch=="}")
        if not depth:return s[loc:i+1]
    raise AssertionError(needle)
def main():
    sup,door,robot=[read(HERE/n) for n in ("Supervisor.cc","DoorClose.cc","RobotContext.cc")]
    # Assert the stack excerpt has the expected own-phase subscription and cleanup,
    # but use neither a stub Rx executor nor a fake live scheduler as stock evidence.
    assert "me->_timer.reset()" in door
    assert "auto me = weak.lock();" in door
    a=door.index("std::chrono::milliseconds(1000),")
    text=(HERE/"fixture.cc.in").read_text()
    glue="\n".join(body(sup,"void Node::"+n+"(") for n in ("_process_open_request",
              "_process_close_request","_send_open_request","_send_close_request","_publish_heartbeat"))
    replacements={"METHODS_SRC":glue,
     "PUBLICATION_SRC":body(door,"void DoorClose::ActivePhase::_publish_close_door()"),
     "TIMER_SRC":body(door[a:],"[weak]()"),
     "RELEASE_SRC":body(robot,"void RobotContext::_release_door(")}
    for k,v in replacements.items():
        assert text.count(k)==1
        text=text.replace(k,v)
    with tempfile.TemporaryDirectory() as d:
        p=Path(d)
        (p/"fixture.cpp").write_text(text)
        (p/"gate_receipt.hpp").write_text(read(HERE/"gate_receipt.hpp"))
        sp.run(["g++","-std=c++20","-O2","-Wall","-Wextra",p/"fixture.cpp","-o",p/"replay"],check=True)
        sp.run([p/"replay"],check=True)
if __name__=="__main__":main()
