"""Extract the authorized benign retirement transition from the same pinned broker."""
from pathlib import Path
src=Path('src1').read_text()
left=src.index('bool Broker::Unregister(')
right=src.index('\n}',left)+2
Path("unregister.inc").write_text(src[:src.index('*/')+2]+'\n'+src[left:right]+'\n')
(p:=Path("replay.cpp")).write_text(p.read_text().replace(
    ' void DispatchMessages();',' void DispatchMessages();\\n bool Unregister(const std::string&);'.replace('\\n','\n')))
(p:=Path("scope.cpp")).write_text(p.read_text().replace("int main(){","int previous_scope_main(){"))
left=src.index('void Broker::OnMessage(const subt::msgs::Datagram')
right=src.index('\n}',left)+2
Path('enqueue.inc').write_text(src[:src.index('*/')+2]+'\n'+src[left:right]+'\n')
(p:=Path('replay.cpp')).write_text(p.read_text().replace(
    ' void DispatchMessages();',' void DispatchMessages();\n void OnMessage(const subt::msgs::Datagram&);'))
