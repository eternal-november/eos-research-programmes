#!/usr/bin/env python3
"""Compile the pinned graph validator with inert local data types, no robot or MQTT."""
import hashlib
import subprocess
import sys
import tempfile
from pathlib import Path


def source(path, digest):
    raw=Path(path).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\x00'+raw).hexdigest()==digest
    return raw.decode()


CPP = r"""
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
#include <cassert>
namespace fmt {
template<class... Ts> std::string format(std::string s, Ts...) {return s;}
}
namespace vda5050_core::types {
struct Node { std::string node_id; uint32_t sequence_id; bool released;
  bool operator==(Node const&) const=default; };
struct Edge { std::string edge_id; uint32_t sequence_id; bool released;
  std::string start_node_id,end_node_id; };
struct Order { std::string order_id; uint32_t order_update_id;
  std::vector<Node> nodes; std::vector<Edge> edges; };
struct ErrorReference {std::string key,value;};
enum class ErrorLevel {FATAL};
}
namespace vda5050_core::errors {
constexpr const char *RefOrderId="oid", *RefOrderUpdateId="uid",
  *RefNodeId="nid", *RefSequenceId="sid", *RefEdgeId="eid",
  *GraphValidationError="graph", *OrderUpdateError="update";
std::string create_error(std::string, std::string desc,
  std::vector<types::ErrorReference>, types::ErrorLevel) {return desc;}
struct ValidationResult { std::vector<std::string> details;
  void add_error(std::string s) {details.push_back(s);}
  explicit operator bool() const {return details.empty();} };
}
"""
TEST = r"""
using namespace vda5050_core;
using namespace std;
types::Order route(uint32_t id, string first, uint32_t seq, string next,bool released) {
  return {"repair",id,{{first,seq,true},{next,seq+2,released}},
    {{first+next,seq+1,released,first,next}}};
}
int main() {
  auto offer=route(0,"A",0,"B",false);
  auto release=route(1,"A",0,"B",true);
  auto replace=route(2,"A",0,"X",true);
  auto append=route(2,"B",2,"X",true);
  assert(validation::is_valid_graph(offer)&&validation::is_valid_graph(release)
      &&validation::is_valid_graph(replace)&&validation::is_valid_graph(append));
  auto adopted = validation::is_valid_update(offer,replace);
  auto cannot_strip = validation::is_valid_update(release,replace);
  auto late_release = validation::is_valid_update(replace,release);
  auto append_after_b = validation::is_valid_update(release,append);
  assert(adopted && !cannot_strip && !late_release && append_after_b);
  assert(cannot_strip.details.size()==1 &&
      cannot_strip.details[0].find("last released node")!=string::npos);
  assert(late_release.details.size()==1 &&
      late_release.details[0].find("strictly increasing")!=string::npos);
  cout << "replacement_first: accept replacement; reject lower update on arrival\n";
  cout << "release_first: reject replacement at old anchor; accept update stitched at B\n";
}
"""


def main(vp, ap, tp):
    v=source(vp,'f8e427852e3afaf357fae7dc3f96dbbe78bc2c9f')
    a=source(ap,'76e71ef7b8e25bb794f258cf5e290004b0fae2ba')
    t=source(tp,'17e390b44b22c103f44cc9058f79351a6bc38f98')
    body=v[v.index('namespace vda5050_core::validation {'):]
    # Check trace provenance, not navigation execution in this harness.
    assert a.index('if (!next_node.released) return;')<a.index('navigation_callback(\n')
    assert 'TEST_F(AdapterNavigationTest, UnreleasedNodeDoesNotDispatch)' in t
    with tempfile.TemporaryDirectory() as d:
        p=Path(d)
        (p/'test.cc').write_text(CPP+body+'\n'+TEST)
        subprocess.run(['c++','-std=c++20','-o',str(p/'test'),str(p/'test.cc')],check=True)
        subprocess.run([str(p/'test')],check=True)


if __name__=='__main__':
    main(*sys.argv[1:])
