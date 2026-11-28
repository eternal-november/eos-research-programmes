from pathlib import Path
s=Path('source/UnackedRpcResults.cc').read_text()
license=s[:s.index('*/')+2]
out=[]
for name in ('bool\nUnackedRpcResults::checkDuplicate(', 'void\nUnackedRpcResults::Client::processAck(', 'void\nUnackedRpcResults::recoverRecord(', 'bool\nUnackedRpcResults::shouldRecover('):
    start=s.index(name)
    end=s.index('\n}',start)+2
    out.append(s[start:end])
Path('server.inc').write_text(license+'\n'+'\n'.join(out)+'\n')
