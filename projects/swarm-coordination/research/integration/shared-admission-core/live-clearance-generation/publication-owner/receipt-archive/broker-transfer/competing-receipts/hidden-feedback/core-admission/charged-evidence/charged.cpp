#define main previous_selected_broker
#include "upstream_replay.cpp"
#undef main

int main(int argc,char**argv) {
 assert(argc==5);
 const auto kind=std::string(argv[1]), medium=std::string(argv[2]);
 const int cert_tick=std::stoi(argv[3]),widen=std::stoi(argv[4]);
 assert(cert_tick>=4 && cert_tick<=6 && widen>=0 && widen<=1);
 World w(16);
 auto add=[&](const std::string& s,unsigned cap){
   auto x=std::make_shared<TeamNode>();
   x->name=s;x->radio=w.b.team->at("P")->radio;x->radio.capacity=8*cap;
   w.b.team->emplace(s,x);w.b.endpoints[s+":7"]={{s}};
 };
 add("R",5+widen);add("Scout",32);add("Side",8);add("Sink",8);add("Witness",8);
 w.b.team->at("P")->radio.capacity=32;
 w.b.team->at("Q")->radio.capacity=32;
 w.b.endpoints["P:7"]={{"P"}};
 std::map<std::string,std::string> held;
 for(std::string s:{"P","Q","R"})
   w.app.callbacks[s+":7"]=[&,s](auto src,auto,auto,auto content){if(src=="Base")held[s]=content;};
 bool certified=false,absence=false,notice=false,settledA=false,settledB=false;
 int atA=-1,atB=-1;
 unsigned independent=0,received=0;
 w.app.callbacks["Scout:7"]=[&](auto src,auto,auto,auto body){
   received+=body.size();
   if(src=="Witness"&&body=="E")certified=true;
   if(src=="Witness"&&body=="X")absence=true;
   if(src=="P"&&body=="AA"){
      settledA=true;atA=int(now*4);
      if(kind=="visible")notice=true;
   }
   if(src=="Q"&&body=="AA"&&!settledA){settledA=true;atA=int(now*4);}
   if(src=="R"&&body=="BBB"&&!settledB){settledB=true;atB=int(now*4);}
 };
 w.app.callbacks["Sink:7"]=[&](auto src,auto,auto,auto d){if(src=="Side"&&d=="W")++independent;};
 auto emit=[&](std::string from,std::string to,std::string body,int t){
   assert(t>=now*4);
   now=t/4.0;w.b.incomingMsgs.push_back({from,to,body});w.b.DispatchMessages();
   assert(w.b.incomingMsgs.empty());
 };
 std::string archived;assert(std::getline(std::cin,archived));
 if(archived.find('A')!=std::string::npos){emit("Base","P","AA",0);emit("Base","Q","AA",1);}
 if(archived.find('B')!=std::string::npos)emit("Base","R","BBB",2);
 std::cout<<"{\"stage\":"<<held.size()<<"}"<<std::endl;
 std::string close;assert(std::getline(std::cin,close)&&close=="closed");
 emit("Side","Sink","W",3);
 // P's first emission slot is tick 4. A source event before it, not
 // membership at a later read, establishes that this send did not happen.
 const bool early=kind=="early"||kind=="silent";
 bool removed_before=false;
 auto remove=[&](bool pre){
   assert(w.b.team->erase("P")==1);
   held.erase("P");removed_before=pre;
 };
 if(early)remove(true);
 if(w.b.team->count("P"))emit("P","Scout",held.at("P"),4);
 if(!early)remove(false);
 if(medium=="radio"){
   if((early&&kind!="silent")||!early)
     emit("Witness","Scout",removed_before?"E":"X",cert_tick);
 } else if(medium=="local"){
   certified=removed_before&&kind!="silent";
   absence=!removed_before;
 } else assert(medium=="none");
 const auto raw=w.state("Scout").bytes_received_this_epoch;
 std::cout<<"{\"known\":"<<notice<<",\"cert\":"<<certified<<",\"absence\":"<<absence
          <<",\"rx\":"<<raw<<"}"<<std::endl;
 std::string schedule;assert(std::getline(std::cin,schedule));
 if(schedule=="B")emit("R","Scout",held.at("R"),8);
 else if(schedule=="QB"){emit("Q","Scout",held.at("Q"),8);emit("R","Scout",held.at("R"),8);}
 else if(schedule=="BQ"){emit("R","Scout",held.at("R"),8);emit("Q","Scout",held.at("Q"),8);}
 else if(schedule=="Q_B"){emit("Q","Scout",held.at("Q"),8);emit("R","Scout",held.at("R"),9);}
 else if(schedule=="B_Q"){emit("R","Scout",held.at("R"),8);emit("Q","Scout",held.at("Q"),9);}
 else if(schedule=="_QB"){emit("Q","Scout",held.at("Q"),9);emit("R","Scout",held.at("R"),9);}
 else if(schedule=="_BQ"){emit("R","Scout",held.at("R"),9);emit("Q","Scout",held.at("Q"),9);}
 else if(schedule=="B_")emit("R","Scout",held.at("R"),9);
 else assert(false);
 std::cout<<"{\"A\":"<<atA<<",\"B\":"<<atB<<",\"received\":"<<received
          <<",\"side\":"<<independent<<"}"<<std::endl;
}
