from pathlib import Path
p=Path("staged_replay.inc")
s=p.read_text()
a=''' bool Request(const std::string&,subt::msgs::Datagram msg){'''
b=''' std::map<std::string,CommsClient*> namedClients;
 bool Request(const std::string& host,subt::msgs::Datagram msg){'''
c='''  return receiver->OnMessageRos(r,res);'''
e='''  auto it=namedClients.find(host);
  return (it==namedClients.end()?receiver:it->second)->OnMessageRos(r,res);'''
assert s.count(a)==1 and s.count(c)==1
p.write_text(s.replace(a,b).replace(c,e))
