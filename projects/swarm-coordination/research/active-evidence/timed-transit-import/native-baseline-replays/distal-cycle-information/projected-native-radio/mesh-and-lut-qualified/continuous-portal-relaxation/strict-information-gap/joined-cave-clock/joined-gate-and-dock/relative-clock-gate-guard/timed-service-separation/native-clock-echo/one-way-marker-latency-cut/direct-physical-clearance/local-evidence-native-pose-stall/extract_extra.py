"""Lift unmodified native membership removal into the existing shim."""
from pathlib import Path
p=Path('staged_replay.inc')
s=p.read_text()
decl=' void DispatchMessages();'
assert s.count(decl)==1
s=s.replace(decl,decl+'\n bool Unregister(const std::string& id);')
c=Path('src1').read_text()
start=c.index('bool Broker::Unregister(')
end=c.index('\n}',start)+2
p.write_text(s+'\n'+c[start:end]+'\n')
