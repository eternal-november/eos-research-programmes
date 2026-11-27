from pathlib import Path
from hashlib import sha1
p=Path('GameLogicPlugin.cc').read_bytes()
assert sha1(b'blob '+str(len(p)).encode()+b'\0'+p).hexdigest()=='f79b759dc7b2f796d873538f165847c4a317c99c'
s=p.decode()
a=s.index('bool GameLogicPluginPrivate::OnNewArtifact(')
b=s.index('void GameLogicPluginPrivate::PublishScore()',a)
Path('score.inc').write_text(s[a:b])
