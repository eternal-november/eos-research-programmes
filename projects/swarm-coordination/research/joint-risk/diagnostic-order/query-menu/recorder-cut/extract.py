from pathlib import Path
import hashlib,sys
root=Path(sys.argv[1])
def exact(n,h):
    b=(root/n).read_bytes()
    assert hashlib.sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==h
    return b.decode()
src=exact("recorder.cpp","19ca101bd808236c4a0daa540ccc5548b3962322")
h=exact("writer.hpp","cace85461c4f5ee0be79d7243bf7858ba4f09c3f")
i=src.index("std::shared_ptr<rclcpp::GenericSubscription>\nRecorderImpl::create_subscription(")
j=src.index("\n}",i)+2
out=src[i:j]
assert "mi.get_rmw_message_info().source_timestamp" in out
a=h.index("const rcutils_time_point_value_t & recv_timestamp,")
assert "uint32_t sequence_number = 0);" in h[a:a+220]
Path(sys.argv[2]).write_text(out+"\n")
