from pathlib import Path
import sys
p=Path(sys.argv[1])
def extract(src,start,end=None):
    s=(p/src).read_text(); i=s.index(start)
    if end is not None:return s[i:s.index(end,i)]
    j=s.index('{',i); d=1; k=j+1
    while d:
        d+=(s[k]=='{')-(s[k]=='}');k+=1
    return s[i:k]+'\n'
Path('logs.inc').write_text(extract('game.cc',
    'void GameLogicPluginPrivate::OnRockFallDeployRemainingEvent'))
Path('detector.inc').write_text(extract('detector.cc',
    '        if (region.Intersects(performerVolume))','\n        return true;'))
Path('deploy.inc').write_text(extract('breadcrumb.cc',
    '    for (std::size_t i = 0; i < cmds.size(); ++i)'))
