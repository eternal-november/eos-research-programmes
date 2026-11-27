
#define main previous_selected_broker
#include "upstream_replay.cpp"
#undef main
int main(int argc,char**argv){
 assert(argc==9);
 const auto barrier=std::string(argv[8]);
 std::string deposited;
 const int a=std::stoi(argv[1]),b=std::stoi(argv[2]);
 const std::vector<int> caps{std::stoi(argv[3]),std::stoi(argv[4]),std::stoi(argv[5])};
 const auto order=std::string(argv[6]),gone=std::string(argv[7]);
 const std::string A(a,'A'),B(b,'B');
 World w(16);
 auto add=[&](const std::string& s,unsigned cap){
  auto x=std::make_shared<TeamNode>();
  x->name=s;x->radio=w.b.team->at("P")->radio;x->radio.capacity=8*cap;
  w.b.team->emplace(s,x);w.b.endpoints[s+":7"]={{s}};
 };
 add("R",caps.at(2));add("Scout",32);add("Side",8);add("Sink",8);
 w.b.team->at("P")->radio.capacity=8*caps[0];
 w.b.team->at("Q")->radio.capacity=8*caps[1];
 w.b.endpoints["P:7"]={{"P"}};
 std::map<std::string,std::string> held;
 for(std::string s:{"P","Q","R"})
  w.app.callbacks[s+":7"]=[&,s](auto src,auto,auto,auto content){if(src=="Base")held[s]=content;};
 std::vector<std::string> arrival;
 std::set<char> paid;
 unsigned independent=0;
 w.app.callbacks["Scout:7"]=[&](auto src,auto,auto,auto content){
   arrival.push_back(src);
   if(src=="P"){
    deposited=content;
    if(barrier=="exposed"&&content==A)paid.insert('A');
   }
   if(src=="Q"&&content==A)paid.insert('A');
   if(src=="R"&&content==B)paid.insert('B');
 };
 w.app.callbacks["Sink:7"]=[&](auto src,auto,auto,auto d){if(src=="Side"&&d=="W")++independent;};
 auto emit=[&](std::string from,std::string to,std::string body,int t){
  now=t/4.0;
  w.b.incomingMsgs.push_back({from,to,body});w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty());
 };
 std::string archived;
 assert(std::getline(std::cin,archived));
 if(archived.find('A')!=std::string::npos){
  emit("Base","P",A,0);emit("Base","Q",A,1);
 }
 if(archived.find('B')!=std::string::npos)emit("Base","R",B,2);
 std::cout<<"{\"A_copies\":"<<held.count("P")+held.count("Q")<<",\"B_copies\":"<<held.count("R")<<"}"<<std::endl;
 std::string next;assert(std::getline(std::cin,next)&&next=="closed");
 emit("Side","Sink","W",4);
 if(gone!="none"){assert(w.b.team->erase(gone)==1);held.erase(gone);}
 std::string attempts;
 auto tryOne=[&](char c){
  const std::string s(1,c);
  if(held.count(s)){
   auto body=(c=='P'&&barrier=="stale")?std::string("AX"):held.at(s);
   emit(s,"Scout",body,5);attempts+=c;
  }
 };
 tryOne('P');
 std::cout<<"{\"deposited\":\""<<deposited<<"\",\"app\":"<<paid.count('A')
          <<",\"rx\":"<<w.state("Scout").bytes_received_this_epoch<<"}"<<std::endl;
 std::string recovered;
 assert(std::getline(std::cin,recovered));
 if(recovered=="recovered"){
   assert(deposited==A);paid.insert('A');
 }else assert(recovered=="none");
 if(order=="Bfirst"){tryOne('R');if(!paid.count('A'))tryOne('Q');}
 else { if(!paid.count('A'))tryOne('Q');tryOne('R'); }
 unsigned tx=0;
 for(const auto* s:{"P","Q","R"})
  if(w.b.team->count(s))tx+=w.state(s).bytes_sent_this_epoch;
 std::string raw;
 for(auto&s:arrival)raw+=s;
 std::cout<<"{\"A\":"<<paid.count('A')<<",\"B\":"<<paid.count('B')
          <<",\"arrivals\":\""<<raw<<"\",\"attempts\":\""<<attempts
          <<"\",\"rx\":"<<w.state("Scout").bytes_received_this_epoch
          <<",\"tx\":"<<tx<<",\"side\":"<<independent<<"}"<<std::endl;
}
