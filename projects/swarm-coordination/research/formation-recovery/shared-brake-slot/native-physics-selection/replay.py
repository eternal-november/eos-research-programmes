#!/usr/bin/env python3
"""Replays the pinned Gazebo Sim joint-command selection and cleanup slices."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
COMMIT = "9b1151a9c1f5fe6d1af4c6e0d33d1f0992e8a811"
PINS = {
    "Physics.cc": ("src/systems/physics/Physics.cc", "7be8b1cd2067be679f9f27a2d689728d51055214"),
    "ApplyJointForce.cc": ("src/systems/apply_joint_force/ApplyJointForce.cc",
                           "c454ca5458bd5d6334de28e10ccd2ea41884ccac"),
}

def read(name):
    path, expected = PINS[name]
    directory = Path(sys.argv[1]) if len(sys.argv)>1 else HERE / "pinned"
    local = directory / name
    data = local.read_bytes() if local.is_file() else subprocess.check_output(
        ["curl","-fLsS",f"https://raw.githubusercontent.com/gazebosim/gz-sim/{COMMIT}/{path}"])
    found = hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()
    if found!=expected:
        raise ValueError(f"{name}: wrong Git blob {found}")
    return data.decode()

def license_of(s):
    return s[:s.index("*/")+2]+"\n"

def main():
    p,w = map(read,PINS)
    # Keep writer method bodies unchanged, omit plugin registration and Configure.
    writer=license_of(w)+w[w.index("void ApplyJointForce::PreUpdate("):
                           w.index("IGNITION_ADD_PLUGIN(ApplyJointForce,")]
    # Entire command/reset choice after joint and DOF lookup through lambda return.
    start=p.index("        auto posReset = _ecm.Component<components::JointPositionReset>")
    end=p.index("\n      });\n\n  // Link wrenches",start)
    select=license_of(p)+p[start:end]+"\n"
    # The actual zeroing callbacks in UpdateSim, with unrelated component types omitted.
    begin=p.index("  // Clear pending commands")
    def cleaner(component):
        start=p.index(f"  _ecm.Each<components::{component}>",begin)
        return p[start:p.index("      });",start)+len("      });")]+"\n"
    cleanup=license_of(p)+cleaner("JointForceCmd")+cleaner("JointVelocityCmd")
    with tempfile.TemporaryDirectory() as tmp:
        t=Path(tmp)
        for name,src in {"force_writer.inc":writer, "physics_choice.inc":select,
                         "physics_clean.inc":cleanup}.items():
            (t/name).write_text(src)
        exe=t/"fixture"
        subprocess.run(["g++","-std=c++17","-O2","-Wall","-Wextra","-Werror","-pthread",
                        "-I"+tmp,str(HERE/"fixture.cc"),"-o",str(exe)],check=True)
        # Missing/short vectors intentionally provoke the upstream diagnostic.
        r=subprocess.run([str(exe)],capture_output=True,text=True)
        if r.returncode:
            print(r.stdout+r.stderr)
            r.check_returncode()
        print(r.stdout,end="")
        print(f"{len(r.stderr.splitlines())} expected diagnostic lines in the negative/error cases")

if __name__=="__main__":
    main()
