#!/usr/bin/env python3
"""Selected native blockade methods with a supplied assignment range."""
import hashlib
import subprocess
import sys
import tempfile
import re
from pathlib import Path


def body(path,sha,pattern):
    p=Path(path).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(p)).encode()+b'\0'+p).hexdigest()==sha
    s=p.decode()
    a=re.search(pattern,s,flags=re.M)
    assert a
    start=a.start()
    left=s.index('{',a.end())
    k=1
    right=left+1
    while k>0:
        k+=(s[right]=='{')-(s[right]=='}')
        right+=1
    return s[start:right]


header=r"""
#include <algorithm>
#include <cassert>
#include <iostream>
#include <map>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using ParticipantId=unsigned;
using ReservationId=unsigned;
using CheckpointId=std::size_t;
struct Status {
  ReservationId reservation=0;
  std::optional<CheckpointId> last_ready;
  CheckpointId last_reached=0;
  bool critical_error=false;
};
struct Writer {
  std::vector<std::string> messages;
  void cancel(unsigned,unsigned) {messages.push_back("CANCEL");}
};
struct Participant {
  struct Implementation {
    struct Shared {
      unsigned _id=1;
      Writer w;
      Writer* _writer=&w;
      std::optional<ReservationId> _reservation_id=2;
      std::optional<CheckpointId> _last_ready=1;
      CheckpointId _last_reached=0;
      void _send_reservation() {w.messages.push_back("SET");}
      void _send_ready() {w.messages.push_back("READY "+std::to_string(*_last_ready));}
      void _send_release(CheckpointId n) {w.messages.push_back("RELEASE "+std::to_string(n));}
      void _send_reached() {w.messages.push_back("REACHED "+std::to_string(_last_reached));}
      void check(Status const&);
    };
  };
};
"""
mod_head=r"""
struct Assignments {
  struct R {CheckpointId begin,end;};
  std::map<unsigned,R> ranges;
  struct Implementation {
    static Assignments& modify(Assignments& a) {return a;}
  };
};
using std::to_string;
std::string toul(unsigned v){return std::to_string(v)+" ";}
struct ModeratorStub {
  struct Recorded {
    ReservationId id=2;
    struct P {std::vector<unsigned> path{0,1,2,3};} reservation;
  };
  std::map<unsigned,Recorded> last_known_reservation{{1,{}}};
  std::map<unsigned,Status> statuses{{1,Status{2,1,0,false}}};
  Assignments assignments{{{1,{0,1}}}};
  void (*info_logger)(const std::string&)=nullptr;
  int wakes=0;
  void process_ready_queue(){++wakes;}
"""
test=r"""
int main() {
  Participant::Implementation::Shared before,after;
  after._last_reached=2;
  const Status mismatch{1,{},0,false};
  before.check(mismatch);
  after.check(mismatch);
  assert(before.w.messages==after.w.messages);
  assert((before.w.messages==std::vector<std::string>{"SET","READY 1"}));
  before.w.messages.clear();
  after.w.messages.clear();
  const Status matched{2,1,0,false};
  before.check(matched);
  after.check(matched);
  assert(before.w.messages.empty());
  assert((after.w.messages==std::vector<std::string>{"REACHED 2"}));
  ModeratorStub m;
  bool caught=false;
  try{m.reached(1,2,2);}catch(const std::runtime_error&){caught=true;}
  assert(caught && m.statuses.at(1).critical_error && m.statuses.at(1).last_reached==0);
  m.reached(1,2,2);
  assert(m.statuses.at(1).last_reached==0 && m.wakes==0);
  m.assignments.ranges.at(1).end=2; // Declared input, not native grant synthesis.
  m.reached(1,2,2);
  assert(m.statuses.at(1).last_reached==2 && m.assignments.ranges.at(1).begin==2 && m.wakes==1);
  std::cout<<"wrong reservation: same SET/READY; matching reservation: REACHED 2 only after progress\n";
  std::cout<<"supplied end 1: repeated REACHED 2 rejected; supplied end 2: accepted\n";
}
"""

if __name__=="__main__":
    p=body(sys.argv[1],"733808821434336850817fc7c9f79886df6e5850",
           r"^void Participant::Implementation::Shared::check\(const Status& status\)")
    m=body(sys.argv[2],"6f7baa24e42780bd38480414ec2a6ef34d57b06a",r"^  void reached\(")
    with tempfile.TemporaryDirectory() as folder:
        d=Path(folder)
        (d/"case.cc").write_text(header+p+mod_head+m+"};\n"+test)
        subprocess.run(["c++","-std=c++20","-Wall","-Wextra","-o",str(d/"case"),str(d/"case.cc")],check=True)
        subprocess.run([str(d/"case")],check=True)
