#!/usr/bin/env python3
"""Extract selected unchanged upstream C++ definitions and run a serial fixture."""
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PINS = {
    "DiffDrive.cc": ("gazebosim/gz-sim", "9b1151a9c1f5fe6d1af4c6e0d33d1f0992e8a811",
                     "src/systems/diff_drive/DiffDrive.cc", "e2fc82492b1c310b414bec776a7ba588e79c9fa7"),
    "SpeedLimiter.cc": ("gazebosim/gz-math", "4ca6553b3ee6cae6696e8abe3aa70ca163274de4",
                        "src/SpeedLimiter.cc", "fe2c1df6f1833721d2765742df6d6511c1cfae84"),
    "SpeedLimiter.hh": ("gazebosim/gz-math", "4ca6553b3ee6cae6696e8abe3aa70ca163274de4",
                        "include/gz/math/SpeedLimiter.hh", "e90ce8f20c8edf1a7431818bd4a7c1906a4d177f"),
    "Helpers.hh": ("gazebosim/gz-math", "4ca6553b3ee6cae6696e8abe3aa70ca163274de4",
                   "include/gz/math/Helpers.hh", "62f79b3119f75760c6574795d5c27d1049598ea4"),
}

def git_blob(data):
    return hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()

def read_source(name):
    repo, commit, path, digest = PINS[name]
    local = Path(sys.argv[1]) / name if len(sys.argv)>1 else HERE / "pinned" / name
    if local.is_file():
        data = local.read_bytes()
    else:
        data = subprocess.check_output(["curl","-fLsS",
            f"https://raw.githubusercontent.com/{repo}/{commit}/{path}"])
    if git_blob(data)!=digest:
        raise ValueError(f"{name}: wrong Git blob {git_blob(data)}")
    return data.decode()

def body(text, label):
    start = text.index(label)
    i = text.index("{", start)
    level = 1
    while level:
        i += 1
        level += (text[i]=="{") - (text[i]=="}")
    return text[start:i+1]

def main():
    dd, speed, decl, helpers = map(read_source,PINS)
    # License headers retained in all generated fragments.
    dh = dd[:dd.index("*/")+2]+"\n"
    sh = speed[:speed.index("*/")+2]+"\n"
    hh = helpers[:helpers.index("*/")+2]+"\n"
    assert "this->dataPtr->enabled = true;" in dd
    fragments = {
        "native_commands.inc": dh+body(dd,"struct Commands")+";\n",
        "native_drive.inc": dh+"\n\n".join(body(dd, x) for x in [
            "void DiffDrive::PreUpdate(", "void DiffDrive::PostUpdate(",
            "void DiffDrivePrivate::UpdateVelocity(", "void DiffDrivePrivate::OnCmdVel(",
            "void DiffDrivePrivate::OnEnable("])+"\n",
        "native_limiter.inc": sh+speed[speed.index("using namespace gz;"):],
        "native_limiter_decl.inc": sh+"namespace ignition::math {\n"
            + "class SpeedLimiterPrivate;\n"
            +body(decl,"class IGNITION_MATH_VISIBLE SpeedLimiter").replace("IGNITION_MATH_VISIBLE ","")
            +";\n}\n",
        "native_helpers.inc": hh+"\n".join("template<typename T>\n"+body(helpers,x)
                    for x in ["inline T clamp(", "inline bool equal("])+"\n"
    }
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp)
        for name,v in fragments.items():
            (p/name).write_text(v)
        obj=p/"radio.o"
        subprocess.run(["bash",str(HERE/"build_radio.sh"),str(obj)],check=True)
        exe = p / "fixture"
        subprocess.run(["g++","-std=c++17","-O2","-Wall","-Wextra","-Werror","-pthread",
                        "-I"+tmp,str(HERE/"fixture.cc"),str(obj),"-o",str(exe)],check=True)
        subprocess.run([str(exe)],check=True)

if __name__ == "__main__":
    main()
