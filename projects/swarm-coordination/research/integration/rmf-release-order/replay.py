from pathlib import Path
import hashlib
import re
import subprocess
import tempfile

PIN = "3be9d5e3d97d8b380255fe0628a30e09265e04e5"

def method(src, name):
    sig = re.search(r"^  void " + name + r"\(", src, re.M)
    assert sig, name
    return src[sig.start(): src.index("\n  }", sig.end())+4]

def main():
    h = Path(__file__).resolve().parent
    raw = (h/"ReservationNode.cpp").read_bytes()
    assert hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()==PIN
    src=raw.decode()
    types=src[src.index("class TicketStore"):src.index("using namespace std::chrono_literals;")]
    shim = r"""
class ReservationNode : public rclcpp::Node {
public:
  using Topic=rmf_reservation_msgs::msg::ReservationAllocation;
  using Ticket=rmf_reservation_msgs::msg::Ticket;
  std::shared_ptr<Sink<Ticket>> ticket_pub_=std::make_shared<Sink<Ticket>>();
  std::shared_ptr<Sink<Topic>> allocation_pub_=std::make_shared<Sink<Topic>>();
  std::unordered_map<std::size_t, std::vector<LocationReq>> requests_, waitpoints_;
  TicketStore ticket_store_;
  CurrentState current_state_;
  ServiceQueueManager queue_manager_;
"""
    with tempfile.TemporaryDirectory() as d:
        d=Path(d)
        (d/"extracted.inc").write_text(types+shim+"\n".join(method(src,x) for x in ("on_request","claim_request","release"))+"\n};\n")
        subprocess.run(["g++","-std=c++17","-O2","-I",str(d),str(h/"harness.cpp"),"-o",str(d/"check")],check=True)
        subprocess.run([str(d/"check")],check=True)

if __name__=="__main__":
    main()
