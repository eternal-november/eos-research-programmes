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

def main():
    here = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as d:
        p = Path(d)
        out = []
        for name, digest in SOURCES.items():
            raw = (here / name).read_bytes()
            assert hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == digest
            out.extend(extract(raw.decode(), key) for key in FUNCTIONS[name])
        (p / "extracted.inc").write_text("\n".join(out))
        subprocess.run(["g++", "-std=c++17", "-O2", "-I", d, str(here/"harness.cpp"), "-o", str(p/"check")], check=True)
        subprocess.run([str(p/"check")], check=True)

if __name__ == "__main__":
    main()
