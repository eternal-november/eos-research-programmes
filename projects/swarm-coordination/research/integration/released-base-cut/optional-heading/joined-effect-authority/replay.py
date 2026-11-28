#!/usr/bin/env python3
from pathlib import Path
import hashlib,subprocess,tempfile,sys
H=Path(__file__).resolve().parent
src={}
for ln in (H/"SOURCE.tsv").read_text().splitlines():
    n,repo,rev,path,sha=ln.split("\t")
    b=(H/"pinned"/n).read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha
    src[n]=b.decode()
def ns(s):
    return s[s.index("namespace vda5050_core {"):].split("#endif")[0]
def fn(s,name):
    i=s.rindex("\n",0,s.index("::"+name+"("))+1
    return s[i:s.index("\n}",i)+2]
f=(H/"fixture.hpp").read_text()
f=f.replace("VDA_NATIVE_NODE_TYPES","\n".join(ns(src[n]) for n in ("node_position.hpp","node.hpp")))
sm,ad=src["state_manager.cpp"],src["adapter.cpp"]
vd=src["order_graph_validator.cpp"]
unit="\n".join(["#include <cmath>\n#include <optional>\n#include <string>\n#include <algorithm>",
                ns(src["transformation.hpp"]),ns(src["transformation.cpp"]),f,
                ns(src["node_request.hpp"]),ns(src["node_request.cpp"]),
                "namespace fmt {template <class... T> std::string format(std::string v,T...){return v;}}",
                vd[vd.index("namespace vda5050_core::validation {"):],
                "namespace vda5050_core::client::adapter {",
                *(fn(sm,n) for n in ("set_position","initialize_position","set_transformation","transformation","state")),
                fn(ad,"subscribe_orders"),fn(ad,"process_navigation"),"}",
                (H/"trace.inc").read_text()])
for ln in (H/"RMF.tsv").read_text().splitlines():
    repo,rev,sha,name=ln.split("\t")
    b=(H/"rmf"/name).read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==sha
rmf=H/"rmf"
impl=rmf/"rmf_traffic/src/rmf_traffic/blockade"
eigen=Path(sys.argv[1]) if len(sys.argv)>1 else H/"eigen3"
assert (eigen/"Eigen/Core").is_file()
with tempfile.TemporaryDirectory() as d:
    path=Path(d)
    (path/"run.cpp").write_text(unit)
    subprocess.run(["c++","-std=c++20","-O1","-I"+str(eigen),
                    "-I"+str(rmf/"rmf_traffic/include"),"-I"+str(rmf/"rmf_utils/include"),
                    "-o",path/"main",path/"run.cpp",H/"crossing.cc",
                    *(impl/f for f in ("Constraint.cpp","Moderator.cpp","Participant.cpp",
                                       "Rectifier.cpp","conflicts.cpp","geometry.cpp"))],check=True)
    subprocess.run([path/"main"],check=True)
