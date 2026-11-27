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
