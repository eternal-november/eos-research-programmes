from pathlib import Path
from hashlib import sha1
import subprocess
import tempfile

PIN = {
    "bt_action_node.hpp": "91b0932813978e3abbe260b85e20cf7bf253b370",
    "controller_server.cpp": "5cd1c1dd936b5cc2d7d92e24c7eaf9a3287dc786",
    "simple_action_server.hpp": "b1cecd920debe8f9c1b8ef360b7d24bb574d34cd",
}

def extract(s,sig,end_sep):
    a=s.index(sig)
    b=s.index(end_sep,a)
    return s[a:b+len(end_sep)]

def main():
    here=Path(__file__).resolve().parent
    src={}
    for f,digest in PIN.items():
        raw=(here/f).read_bytes()
        assert sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()==digest
        src[f]=raw.decode()
    b=src["bt_action_node.hpp"]
    c=src["controller_server.cpp"]
    s=src["simple_action_server.hpp"]
    with tempfile.TemporaryDirectory() as d:
        p=Path(d)
        files={
            "bt.inc": "\n".join(extract(b,x,"\n  }") for x in ("  void halt() override", "  bool should_cancel_goal()")),
            "server.inc": "\n".join(extract(s,x,"\n  }") for x in ("  bool is_cancel_requested() const","  void terminate_all(","  void terminate(\n")),
            "controller.inc": "\n".join(extract(c,x,"\n}") for x in ("void ControllerServer::publishZeroVelocity()", "void ControllerServer::onGoalExit(")),
            "poll.inc":extract(c,"      if (action_server_->is_cancel_requested()) {","\n      }"),
        }
        for f,v in files.items():(p/f).write_text(v+"\n")
        subprocess.run(["g++","-std=c++17","-O2","-I",d,str(here/"harness.cpp"),"-o",str(p/"probe")],check=True)
        subprocess.run([str(p/"probe")],check=True)
if __name__=="__main__":
    main()
