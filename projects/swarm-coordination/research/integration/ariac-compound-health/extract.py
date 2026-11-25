"""Reproduce writes before the first erase; do not run invalidated iterators."""
import hashlib
from pathlib import Path
import sys

def checked(path, oid):
    b = Path(path).read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest() == oid, path
    return b.decode()

def body(src, name):
    mark = f"TaskManagerPlugin::{name}("
    start = src.index(mark)
    start = src.rfind("    void",0,start)
    end = src.index("\n    }",start)+6
    return src[start:end]

def extract(src):
    out = [body(src,n) for n in ["SetSensorsHealth","SetRobotsHealth",
           "ProcessTemporalRobotMalfunctions","ProcessTemporalSensorBlackouts",
           "UpdateSensorsHealth","UpdateRobotsHealth"]]
    for n in ["ProcessInProgressRobotMalfunctions","ProcessInProgressSensorBlackouts"]:
        fn = body(src,n)
        begin = fn.index("                    impl_->in_progress_")
        end = fn.index(");",begin)+2
        assert ".erase(std::remove(" in fn[begin:end]
        out.append(fn[:begin]+"                    throw BeforeErase{};"+fn[end:])
    return "\n".join(out)

if __name__ == "__main__":
    print(extract(checked(sys.argv[1],"4b6bc2cea406d4813145d9f565318a4ebe345be8")))
