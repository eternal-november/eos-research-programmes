#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main(){
  int early,late,drop;
  while(std::cin>>early>>late>>drop){
    assert(early>=0&&early<=255&&late>=-2&&late<=255);
    now=0.;
    TimedSource w(.5);
    int receivedEarly=-1,receivedLate=-1;
    unsigned r1=0,r2=0,other=0;
    w.bind("Prefix","Second",r1);
    w.bind("Answer","Second",r2);
    w.bind("Unrelated","Far",other);
    w.plant.app.callbacks["Prefix:7"]=[&](auto,auto,auto,const auto& msg){
        assert(msg.size()==1);receivedEarly=(unsigned char)msg[0];++r1;
    };
    w.plant.app.callbacks["Answer:7"]=[&](auto,auto,auto,const auto& msg){
        assert(msg.size()==1);receivedLate=(unsigned char)msg[0];++r2;
    };
    auto send=[&](std::string app,int n,int step,bool fail) {
        now=step/8.;
        w.plant.path_available=!fail;
        w.plant.b.incomingMsgs.push_back({"P",app,std::string(1,(char)n)});
        w.plant.b.DispatchMessages();
        assert(w.plant.b.incomingMsgs.empty());
        w.plant.path_available=true;
    };
    send("Prefix",early,0,false);
    if(late==-2){
      std::cout<<"early "<<receivedEarly<<std::endl;
      assert(bool(std::cin>>late)&&late>=-1&&late<=255);
    }
    if(late>=0)send("Answer",late,2,drop);
    w.dispatch({"Independent","Unrelated",1,3/8.,true});
    assert(r1==1&&other==1&&r2==unsigned(late>=0&&!drop));
    std::cout<<receivedEarly<<' '<<receivedLate<<' '
             <<w.plant.state("P").bytes_sent_this_epoch<<' '
             <<w.plant.state("Second").bytes_received_this_epoch<<' '<<other<<'\n';
  }
}
