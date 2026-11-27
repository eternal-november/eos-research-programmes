"""Use a mock register bus with the unmodified pinned Adafruit Python driver."""
from types import ModuleType
from pathlib import Path
import sys,json
from menu import M,PAIRS,verify

class Bus:
    def __init__(self,pins,flip=False):
        self.pins=tuple(pins)
        self.epoch=0
        self.flip=flip
        self.start=[]
        self.ready=[]
        self.tx=[]
        self.cfg=0x0583
        self.busy=0
        self.res=0
    def __enter__(self):return self
    def __exit__(self,*args):return False
    def write(self,payload):
        address=payload[0]
        u=int.from_bytes(payload[1:],'big')
        self.tx.append(('write',address,u))
        if address!=1:return
        self.cfg=u&0x7fff
        if u&0x8000:
            assert not self.busy
            mux=(u>>12)&7
            raw=sum(a*b for a,b in zip(M[mux],self.pins))
            assert -2048<=raw<2048
            self.res=(raw<<4)&0xffff
            self.start.append((mux,self.epoch))
            self.busy=1
    def write_then_readinto(self,command,buf,in_end):
        address=command[0]
        assert in_end==2
        if address==1:
            if self.busy:
                self.busy=0
                v=self.cfg
                if self.flip:self.epoch+=1
                self.ready.append(self.epoch)
            else:v=self.cfg|0x8000
        else:
            assert address==0 and not self.busy
            v=self.res
        self.tx.append(('read',address,v))
        buf[:2]=v.to_bytes(2,'big')

def install_mock():
    for name in ('micropython','adafruit_bus_device','adafruit_bus_device.i2c_device','busio'):
        sys.modules[name]=ModuleType(name)
    sys.modules['micropython'].const=lambda x:x
    sys.modules['busio'].I2C=object
    sys.modules['adafruit_bus_device.i2c_device'].I2CDevice=lambda b,address:b

def run(pins,modes,flip=False):
    from adafruit_ads1x15.ads1015 import ADS1015
    from adafruit_ads1x15.analog_in import AnalogIn
    bus=Bus(pins,flip)
    dev=ADS1015(bus,gain=1)
    at=len(bus.tx)
    values=[]
    for i in modes:
        channel=AnalogIn(dev,*PAIRS[i]) if i<4 else AnalogIn(dev,i-4)
        values.append(channel.value>>4)
    assert [i for i,_ in bus.start]==list(modes)
    assert len(bus.tx)-at==4*len(modes)
    assert values==[sum(a*b for a,b in zip(M[i],pins)) for i in modes]
    return dict(codes=values,starts=bus.start,ready_epoch=bus.ready,
                transactions=bus.tx[at:],
                qualified=all(a==b for (_,a),b in zip(bus.start,bus.ready,strict=True)))

def main(up):
    install_mock()
    lo,hi=(250,250,120,75),(350,350,120,75)
    a,b=(run(x,(0,)) for x in (lo,hi))
    assert a['codes']==b['codes']==[0]
    singles=[run(x,(4,5)) for x in (lo,hi)]
    assert sum(singles[0]['codes'])<600<sum(singles[1]['codes'])
    singlepair=run((300,200,120,75),(4,5))
    diff=run((300,200,120,75),(0,))
    common=run((330,230,120,75),(0,))
    assert diff['codes']==common['codes']==[100]
    assert 100==singlepair['codes'][0]-singlepair['codes'][1]
    reversed_pair=run((200,300,120,75),(0,))
    assert reversed_pair["codes"]==[-100]
    torn=run((300,200,120,75),(0,),True)
    assert torn['codes']==diff['codes'] and not torn['qualified']
    allmux=[run((300,200,120,75),(i,)) for i in range(8)]
    return dict(menu=verify(up/'force_control.py'),all_mux=allmux,
                same_sign=[diff,singlepair,common],opposite_sign=[a,b,*singles],
                torn_epoch=torn,reversed_pair=reversed_pair)
if __name__=='__main__':print(json.dumps(main(Path(sys.argv[1])),sort_keys=True))
