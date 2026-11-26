#!/usr/bin/env python3
"""Replay selected pinned Open-RMF code, with an authored ordered executor."""
from pathlib import Path
import hashlib
import subprocess
import sys
from tempfile import TemporaryDirectory

src = Path(sys.argv[1]).resolve()
here = Path(__file__).resolve().parent

def read(name, expected):
    b = (src/name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest() == expected
    return b.decode()

def cut(s, start, end):
    i = s.index(start)
    return s[i:s.index(end, i)+len(end)]

full = read("full_control.cpp", "294f008fd9d508b97bdd9c449b3db556c81d9dea")
fleet = read("FleetUpdateHandle.cpp", "4236e6d35f8e7d1914085e2fb7c4065a713b3858")
robot = read("RobotUpdateHandle.cpp", "989012318cdbbd01d45604f7c8c05af09be078c1")
program = (here/"fixture.inc").read_text()
segments = {
    "OPEN": cut(fleet, "void FleetUpdateHandle::open_lanes", "\n}"),
    "CLOSE": cut(fleet, "void FleetUpdateHandle::close_lanes", "\n}"),
    "REPLAN": cut(robot, "void RobotUpdateHandle::replan()", "\n}"),
    "ROBOT": cut(full, "  void newly_closed_lanes(", "\n  }"),
    "CALLBACK": cut(full, "[w = connections->weak_from_this(), fleet_name](\n      rmf_fleet_msgs::msg::LaneRequest", "\n    }"),
}
for label, code in segments.items():
    assert program.count("/*"+label+"*/") == 1
    program = program.replace("/*"+label+"*/", code)
with TemporaryDirectory() as tmp:
    f = Path(tmp)/"test.cpp"
    f.write_text(program)
    run = Path(tmp)/"test"
    subprocess.run(["c++","-std=c++20","-Wall","-Wextra","-Werror",str(f),"-o",str(run)],check=True)
    subprocess.run([str(run)],check=True)
