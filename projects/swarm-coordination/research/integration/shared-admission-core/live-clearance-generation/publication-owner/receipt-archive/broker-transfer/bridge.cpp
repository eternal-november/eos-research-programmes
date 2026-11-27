
#define main previous_broker_main
#include "upstream_replay.cpp"
#undef main

int main(int argc,char** argv){
 assert(argc==7);
 const bool copy=std::string(argv[1])=="copy";
 const bool fail=std::string(argv[2])=="fail";
 const bool erase=std::string(argv[3])=="erase";
 const std::string encoding=argv[4];
 const bool lostNotice=std::string(argv[5])=="mute";
 const auto workload=std::string(argv[6]);
 World w(5);
 auto add=[&](const std::string& n,unsigned c){
  auto x=std::make_shared<TeamNode>();
  x->name=n;x->radio=w.b.team->at("P")->radio;x->radio.capacity=8*c;
  w.b.team->emplace(n,x);w.b.endpoints[n+":7"]={{n}};
 };
 for(auto id:{"Scout","Maint","Side","SideSink","QSink"})add(id,10);
 w.b.endpoints["P:7"]={{"P"}};
 std::map<std::string,std::string> carries;
 for(std::string i:{"P","Q"})
  w.app.callbacks[i+":7"]=[&,i](auto src,auto,auto,auto d){if(src=="Base"&&d=="A1")carries[i]=d;};
 unsigned unrelated=0,raw=0,older=0;
 std::string designated;
 int received=-1;
 w.app.callbacks["Scout:7"]=[&](auto src,auto,auto,auto d){
  if(src=="Maint"&&(d=="M-P"||d=="M-Q"))designated=d.substr(2);
  else {
   ++raw;
   if(src==designated&&(d=="A1"||d=="AC1"))received=int(now*4);
  }
 };
 w.app.callbacks["SideSink:7"]=[&](auto from,auto,auto,auto d){if(from=="Side"&&d=="U01")++unrelated;};
 w.app.callbacks["QSink:7"]=[&](auto from,auto,auto,auto d){if(from=="Q"&&d=="U004")++older;};
 auto emit=[&](const std::string &src,const std::string &dst,const std::string &body,int t,bool good=true){
  now=t/4.0;w.path_available=good;
  w.b.incomingMsgs.push_back({src,dst,body});
  w.b.DispatchMessages();assert(w.b.incomingMsgs.empty());
 };
 std::string payload,next;
 // The only source of A1 is the named positive produced upstream.
 assert(std::getline(std::cin,payload));
 int charge=0;
 if(workload=="early")emit("Q","QSink","U004",0);
 if(payload=="A1"){
   emit("Base","P",payload,0);charge+=2;
   if(copy){emit("Base","Q",payload,1,!erase);charge+=2;}
 }else assert(payload=="none");
 std::cout<<"{\"P\":"<<carries.count("P")<<",\"Q\":"<<carries.count("Q")
          <<",\"stage_bytes\":"<<charge<<"}"<<std::endl;
 // An actual closure receipt from the original native scorer advances
 // this scenario. Failure of the primary occurs after the stage cut.
 assert(std::getline(std::cin,next)&&next=="closed");
 emit("Side","SideSink","U01",3);
 if(workload=="late")emit("Q","QSink","U004",3);
 // The second fault removes the primary sender and its physically held copy.
 if(fail){w.b.team->erase("P");carries.erase("P");}
 const std::string selected=fail?"Q":"P";
 emit("Maint","Scout","M-"+selected,4,!lostNotice);
 if(!designated.empty()&&carries.count(designated)){
   assert(designated==selected);
   // Each byte format resolves to the same current key in this episode.
   auto wire=encoding=="stale"?"A0":encoding=="short"?carries.at(designated):"AC1";
   emit(designated,"Scout",wire,encoding=="wait"?9:5);
 }
 assert(unrelated==1&&older==(workload=="off"?0:1));
 std::cout<<"{\"receipt\":"<<received<<",\"raw\":"<<raw<<",\"other\":"<<unrelated
          <<",\"older\":"<<older<<",\"egress\":"<<(received>=0?received+3:9)<<"}"<<std::endl;
}
