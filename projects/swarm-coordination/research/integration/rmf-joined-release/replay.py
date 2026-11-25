from pathlib import Path
import hashlib
import re
import subprocess
import tempfile

SOURCES = {
    "Node.cpp": "830c416de07d5c33875c9f83b94850138a4e1c7d",
    "ZoneReservationClient.cpp": "93a5d828161e49a3512a810a8f2308df13f36bb0",
}
FUNCTIONS = {
    "Node.cpp": [
        "Node::_process_arrived", "Node::_process_handback", "Node::_process_exit",
        "Node::_zone_pool_is_idle", "Node::_sweep_idle_zone_pools",
    ],
    "ZoneReservationClient.cpp": [
        "ZoneReservationClient::is_available", "ZoneReservationClient::transfer",
        "ZoneReservationClient::confirm_handback", "ZoneReservationClient::_disown",
        "ZoneReservationClient::release", "ZoneReservationClient::release_zone",
        "ZoneReservationClient::has_holdings", "ZoneReservationClient::transferred_vertices",
        "ZoneReservationClient::zones_with_holdings",
    ],
}

def extract(src, name):
    signature = re.search(r"^[^\n]*\b" + re.escape(name) + r"\(", src, re.M)
    assert signature, name
    start = signature.start()
    # Definitions at this pin use a column-zero terminating outer brace.
    end = src.index("\n}", signature.end()) + 2
    return src[start:end]

PIN = "3be9d5e3d97d8b380255fe0628a30e09265e04e5"

def method(src, name):
    sig = re.search(r"^  void " + name + r"\(", src, re.M)
    assert sig, name
    return src[sig.start(): src.index("\n  }", sig.end())+4]


def main():
    here = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as d:
        p = Path(d)
        out = []
        for name, digest in SOURCES.items():
            raw = (here / name).read_bytes()
            assert hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == digest
            out.extend(extract(raw.decode(), key) for key in FUNCTIONS[name])
        (p / "zone.inc").write_text("\n".join(out))
        raw = (here/"ReservationNode.cpp").read_bytes()
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

        (p/"reservation.inc").write_text(types+shim+"\n".join(method(src,x) for x in ("on_request","claim_request","release"))+"\n};\n")
        subprocess.run(["g++", "-std=c++17", "-O2", "-I", d, str(here/"harness.cpp"), "-o", str(p/"check")], check=True)
        subprocess.run([str(p/"check")], check=True)

if __name__ == "__main__":
    main()
