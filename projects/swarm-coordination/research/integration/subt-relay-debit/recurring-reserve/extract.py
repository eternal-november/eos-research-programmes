from pathlib import Path
from hashlib import sha1
from re import search
pins=['e010ad0e8f58210137e92bdd5bf3c8866972e20e','14bcee7b7cad714e2395bed4786236a56bba2a4a','2ff8eab8934cadc5476313b738db3889de262018','029f3dc1403a39a491f0617409689afa819838fb','c52cf9cd00d221680d521bd70cdccbc64195881e','509f3bb9ad6731259e6c00296cf08f681257995a']
s=[]
for i,h in enumerate(pins):
    b=Path(f'src{i}').read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==h
    s.append(b.decode())
def get(i,a):
    src=s[i]
    start=src.index(a)
    op=src.index('\n{',start)
    end=src.index('\n}',op)+2
    return src[start:end]+'\n'
def write(i,name,body):
    Path(name).write_text(s[i][:s[i].index('*/')+2]+'\n'+body)
write(5,'radio.inc',s[5][s[5].index('inline double dbmToPow'):s[5].index('\n}\n',s[5].index('return std::make_tuple(true, rx_power, usingBreadcrumbs);'))+3])
write(0,'drop.inc',get(0,'void CommsBrokerPlugin::UpdateIfNewBreadcrumbs()'))
write(1,'dispatch.inc',get(1,'void Broker::DispatchMessages()'))
write(2,'ros-receipt.inc',get(2,'bool CommsClient::OnMessageRos('))
