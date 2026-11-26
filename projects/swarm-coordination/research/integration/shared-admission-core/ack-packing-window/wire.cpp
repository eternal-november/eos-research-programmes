#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
  int mode,aS,aR,dS,dR,eraseA,eraseD,need,stale,bitY,bitB,inline_run;
  while(std::cin>>mode>>aS>>aR>>dS>>dR>>eraseA>>eraseD>>need>>stale>>bitY>>bitB>>inline_run){
    now=0.;
    TimedSource t(.5);
    unsigned a=0,d=0,ack=0,carry=0;
    int early=-1,seenY=-1,seenB=-1;
    t.bind("Prelude",aR?"Base":"Second",a);
    t.bind("Data",dR?"Base":"Second",d);
    t.bind("Final","Base",carry);
    t.bind("IndependentDue","Far",ack);
    t.plant.app.callbacks["Prelude:7"]=[&](auto,auto,auto,const auto& msg){
        assert(msg.size()==1);++a;
        auto k=(unsigned char)msg[0];
        if(k&2){early=k&1;seenY=early;}
    };
    t.plant.app.callbacks["Data:7"]=[&](auto,auto,auto,const auto& msg){
        assert(msg.size()==1);++d;
        auto k=(unsigned char)msg[0];
        if(mode!=1){
           if(k&4){seenY=k&1;seenB=(k>>1)&1;if(mode==2)early=seenY;}
        }else if(k&2&&seenY>=0)seenB=k&1;
    };
    auto send=[&](std::string from,std::string addr,int at,int byte,bool erase){
        now=at/8.;
        t.plant.path_available=!erase;
        t.plant.b.incomingMsgs.push_back({from,addr,std::string(1,(char)byte)});
        t.plant.b.DispatchMessages();
        assert(t.plant.b.incomingMsgs.empty());
        t.plant.path_available=true;
    };
    t.dispatch(t.preceding); // same P→Base 2-byte carried prefix across all options
    if(mode==1)send(aS?"P":"Q","Prelude",2,bitY+2*int(!stale),eraseA);
    if(mode==2)send(dS?"P":"Q","Data",2,bitY+2*bitB+4*int(!stale),eraseD);
    bool held=need&&early<0;
    if(inline_run){
        std::cout<<"prior "<<held<<' '<<early<<std::endl;
        int next=0;assert(bool(std::cin>>next)&&next==1);
    }
    int packet=(mode==1)?bitB+2:bitY+2*bitB+4*int(!stale);
    if(mode!=2)send(dS?"P":"Q","Data",4,packet,eraseD);
    auto tx=t.plant.state("P").bytes_sent_this_epoch;
    auto rx=t.plant.state("Base").bytes_received_this_epoch;
    t.dispatch({"P","Final",2,6/8.,true});
    t.dispatch({"Independent","IndependentDue",1,7/8.,true});
    std::cout<<a<<' '<<d<<' '<<early<<' '<<seenY<<' '<<seenB<<' '<<held
             <<' '<<tx<<' '<<rx<<' '<<carry<<' '<<ack<<' '<<t.first<<'\n';
  }
}
