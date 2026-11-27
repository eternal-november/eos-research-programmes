"""Expose selected pinned ingress and isolate the earlier fixture entry point."""
from pathlib import Path
src=Path('src1').read_text()
anchor='void Broker::OnMessage(const subt::msgs::Datagram'
assert src.count(anchor)==1
left=src.index(anchor)
right=src.index('\n}',left)+2
Path('enqueue.inc').write_text(src[:src.index('*/')+2]+'\n'+src[left:right]+'\n')
p=Path('replay.cpp')
s=p.read_text()
key=' void DispatchMessages();'
assert s.count(key)==1
p.write_text(s.replace(key,key+'\n void OnMessage(const subt::msgs::Datagram&);'))
p=Path('scope.cpp')
s=p.read_text()
assert s.count('int main(){')==1
p.write_text(s.replace('int main(){','int previous_scope_main(){'))
# Instrument the existing native fixture by passing its own unchanged radio
# function through the following observation wrapper.
p=Path('prior.cpp')
s=p.read_text()
needle='  auto &b=f.w.b;'
assert s.count(needle)==1
s=s.replace(needle,needle+'\n  tap(b);')
needle='  auto sample=[&](double time){'
assert s.count(needle)==1
s=s.replace(needle,'  tap_callbacks(f.w.app);\n'+needle)
Path('observed.inc').write_text(s)
p=Path('observed.inc')
s=p.read_text()
assert s.startswith('#include "scope.cpp"\n#include "enqueue.inc"\n')
p.write_text(s.split('\n',2)[2])
p=Path('observed.inc')
s=p.read_text()
assert s.endswith('}\n')
p.write_text(s[:-2]+'  return 0;\n}\n')
