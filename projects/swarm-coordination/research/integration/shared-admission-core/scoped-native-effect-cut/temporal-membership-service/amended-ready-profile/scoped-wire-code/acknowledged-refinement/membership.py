"""Lift pinned native Register/Unregister into the source replay shim."""
from pathlib import Path
p=Path('staged_replay.inc')
s=p.read_text()
d=" void DispatchMessages();"
assert s.count(d)==1 and s.count('struct TeamNode {')==1
s=s.replace('struct TeamNode {','struct TeamNode {\n std::string address;')
s=s.replace(d,d+"\n bool Register(const std::string& id);\n bool Unregister(const std::string& id);\n radio_configuration default_radio_configuration;")
base=Path('src1').read_text()
start=base.index('bool Broker::Register(')
end=base.index('bool Broker::OnAddrRegistration(',start)
p.write_text(s+'\nusing TeamMember=TeamNode;\n'+base[start:end]+'\n')
