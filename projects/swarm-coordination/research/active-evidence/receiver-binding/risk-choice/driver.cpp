#define main inherited_replay_main
#include "subt/replay.cpp"
#undef main

struct Effects{bool probe,paid,next;unsigned txProbe,txDuty,rxDuty;};

Effects one(int C,int q,int cp,int x,int y,int z,bool same,bool shared,bool dropout){
 World w(C);
 unsigned probe=0,old=0,next=0,initial=0;
 auto newTeam=[&](std::string name,unsigned cap){
    auto n=std::make_shared<TeamNode>(*w.b.team->at("Base"));
    n->name=name;n->radio.capacity=8*cap;w.b.team->emplace(name,n);
 };
 newTeam("T",C);newTeam("Second",C);
 if(!same)w.b.team->at("Q")->radio.capacity=8*cp;
 else assert(cp==C);
 w.b.endpoints["A:7"].push_back({"Base"});
 w.b.endpoints["Bprobe:7"].push_back({shared?"Base":"Second"});
 w.b.endpoints["Bactual:7"].push_back({shared?"Base":"Second"});
 w.b.endpoints["Bnext:7"].push_back({shared?"Base":"Second"});
 w.app.callbacks["Bnext:7"]=[&](auto,auto,auto,const auto&){++next;};
 w.app.callbacks["A:7"]=[&](auto,auto,auto,const auto&){++initial;};
 w.app.callbacks["Bprobe:7"]=[&](auto,auto,auto,const auto&){++probe;};
 w.app.callbacks["Bactual:7"]=[&](auto,auto,auto,const auto&){++old;};
 auto push=[&](std::string src,std::string dst,int len){
    w.b.incomingMsgs.push_back({src,dst,std::string(len,'b')});
    w.b.DispatchMessages();
    assert(w.b.incomingMsgs.empty());
 };
 now=0;
 if(q>0)push("T","A",q);
 assert(initial==static_cast<unsigned>(q>0));
 assert(w.state("Base").bytes_received_this_epoch==q);
 w.path_available=!dropout;
 if(x>0)push(same?"P":"Q","Bprobe",x);
 w.path_available=true;
 unsigned spent=w.state(same?"P":"Q").bytes_sent_this_epoch;
 push("P","Bactual",y);
 push("P","Bnext",z);
 return {probe==1,old==1,next==1,spent,
         static_cast<unsigned>(w.state("P").bytes_sent_this_epoch),
         static_cast<unsigned>(w.state(shared?"Base":"Second").bytes_received_this_epoch)};
}

int main(){
 int C,q,cp,x,y,k,same,shared,drop;
 while(std::cin>>C>>q>>cp>>x>>y>>k>>same>>shared>>drop){
    auto z=one(C,q,cp,x,y,k,same,shared,drop);
    std::cout<<z.probe<<' '<<z.paid<<' '<<z.next<<' '<<z.txProbe<<' '<<z.txDuty<<' '<<z.rxDuty<<std::endl;
 }
}
