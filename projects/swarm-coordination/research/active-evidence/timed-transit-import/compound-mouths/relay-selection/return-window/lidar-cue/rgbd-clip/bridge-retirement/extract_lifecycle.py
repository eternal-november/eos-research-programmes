from pathlib import Path as P
from hashlib import sha1
from xml.etree import ElementTree as XML
import re

for line in P("LIFECYCLE_INPUTS.tsv").read_text().splitlines():
    f,_,_,_,want=line.split("\t")
    data=P(f).read_bytes()
    assert sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==want,f

def block(s,k,b=0):
    a=s.index(k,b)
    i=s.index("{",a)
    depth=0
    for j in range(i,len(s)):
        depth+=(s[j]=="{")-(s[j]=="}")
        if depth==0:return s[a:j+1]
    raise ValueError(k)

a=P("bridge.cpp").read_text()
handler=block(a,"class Handler")+";\n"
assert "_ign_node->Subscribe(" in handler
assert "handlers.push_back(std::make_shared<Handler>(topic, it_node, ign_node));" in a
launch=XML.parse("vehicle_topics.launch")
nodes={n.get("name"):n for n in launch.findall(".//node")}
bridge=nodes["ros_ign_image_depth"]
assert (bridge.get("pkg"),bridge.get("type"))==("ros_ign_image","image_bridge")
prefix,relative=bridge.get("args").split(")/",1)
assert prefix=="$(arg sensor_prefix" and relative=="camera_front/depth_image"
assert nodes["ros_ign_bridge_rgbd"].get("args").startswith("$(arg sensor_prefix)/camera_front/points@")
assert nodes["optical_frame_publisher_depth"].get("args")=="depth"
assert "ros-melodic-ros-ign" in P("dockerfile").read_text()
assert 'getNumSubscribers() == 0u' in P("optical.cc").read_text()
P("bridge.inc").write_text(handler+'\n'+f'constexpr auto depthTopic = "/fixture/{relative}";\n')

h=P("topicstorage.hh").read_text()
h=re.sub(r'^#include "ignition/transport/[^"]+"$',"",h,flags=re.M)
const=re.search(r'const std::string kGenericMessageType = "[^"]+";',P("types.hh").read_text())[0]
P("storage.inc").write_text(const+"\n"+h)
node=P("node.cc").read_text()
shared=P("shared.cc").read_text()
discovery=P("discovery.hh").read_text()
register=block(shared,"void NodeShared::OnNewRegistration")
unregister=block(shared,"void NodeShared::OnEndRegistration")
disconnect=block(shared,"void NodeShared::OnNewDisconnection")
has=block(node,"bool Node::Publisher::HasConnections() const")
timeout=block(discovery,"for (auto const &uuid : uuids)",discovery.index("void UpdateActivity()"))
bye=block(discovery,"if (disconnectCb)",discovery.index("case msgs::Discovery::BYE:"))
# Invoke the selected source emission blocks, not the discovery clock, sockets, or receive loop.
P("transport.inc").write_text("\n".join((register,unregister,disconnect,has,
'''void expire(NodeShared& s,const std::string& id) {
 using Pub=MessagePublisher;
 std::vector<std::string> uuids{id};
 auto disconnectCb=[&](const Pub& pub){s.OnNewDisconnection(pub);};
'''+timeout+"}\n",
'''void bye(NodeShared& s,const std::string& recvPUuid) {
 using Pub=MessagePublisher;
 std::function<void(const Pub&)> disconnectCb=[&](const Pub& pub){s.OnNewDisconnection(pub);};
'''+bye+"}\n")))
