from pathlib import Path
p=Path("replay.cpp")
s=p.read_text()
anchor=" void DispatchMessages();"
assert s.count(anchor)==1
p.write_text(s.replace(anchor,anchor+"""
 bool Bind(const std::string&, const std::string&);
 bool Unregister(const std::string&);
 std::function<bool(const std::string&)> beforeBind;
"""))
src=Path("src1").read_text()
def extract(name):
    i=src.index("bool Broker::"+name+"(")
    return src[i:src.index("\n}",src.index("\n{",i))+2]
license=src[:src.index("*/")+2]
binding=extract("Bind")
before="  BrokerClientInfo clientInfo;"
assert binding.count(before)==1
binding=binding.replace(before,
    "  if (this->beforeBind && !this->beforeBind(_endpoint)) return false;\n"+before)
Path("binding.inc").write_text(license+"\n"+binding+"\n"+extract("Unregister")+"\n")
