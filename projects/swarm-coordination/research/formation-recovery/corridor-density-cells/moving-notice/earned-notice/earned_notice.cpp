
#define main previous_selected_transport
#include "upstream_replay.cpp"
#undef main

// The same fixed-point variables as the movement replay, in 9x units.
std::pair<double,double> profile(double H,double t){
 if(t<=H/2)return {t*t,2*t};
 return {H*H/2-(H-t)*(H-t),2*(H-t)};
}
std::pair<double,double> central9(double t,bool followedLeft){
 if(t<=.75)return {8*t*t,16*t};
 if(t<=1.5)return {9-8*(1.5-t)*(1.5-t),16*(1.5-t)};
 if(t<=2 || !followedLeft){
  auto [p,v]=profile(1.5,t-1.5);
  return {9-9*p,-9*v};
 }
 if(t<=2.5){double u=t-2;return {27.0/4-9*u+9*u*u,-9+18*u};}
 return {4.5,0};
}
std::pair<double,double> policy(double t,int signal){
 auto L=central9(t,true),R=central9(t,false);
 if(signal==1)return {5*L.first,5*L.second};
 if(signal==-1)return {5*R.first,5*R.second};
 return {L.first+4*R.first,L.second+4*R.second};
}
struct Gate {
 // A current, configured civil inspection demand is held by the beacon.
 int current;
 bool narrow, stale, erasure;
 // Plant integration supplies past extrema at the read cut, not future intent.
 bool authorized(double low,double high) const {
  return low>=33.75&&high<=(narrow?44.75:45.0);
 }
 std::string read() const {
  return std::string(1,current==1?'+':'-')+(stale?"6":"7");
 }
};
int record(int demand,bool narrow,bool stale,bool erased,int loadMode){
 World w(5);
 int signal=0,arrivalCount=0;
 w.app.callbacks["Q:7"]=[&](auto sender,auto,auto,auto bytes){
  ++arrivalCount;
  if(sender=="P" && bytes=="+7")signal=1;
  if(sender=="P" && bytes=="-7")signal=-1;
 };
 if(loadMode!=0)assert(w.send("P","Base",4,loadMode==1?1.0:.875));
 assert(w.recv==(loadMode==0?0:1));
 Gate g{demand,narrow,stale,erased};
 // This plant segment is monotone on each of [1,1.5] and [1.5,2].
 double low=std::min(policy(1,0).first,policy(2,0).first);
 double high=policy(1.5,0).first;
 assert(low==33.75 && high==45.0);
 if(g.authorized(low,high)){
  auto payload=g.read();
  now=2;w.path_available=!g.erasure;
  w.b.incomingMsgs.push_back({"P","Q",payload});
  w.b.DispatchMessages();assert(w.b.incomingMsgs.empty());
 }
 const bool raw=!narrow&&!erased&&loadMode!=1;
 assert((arrivalCount==1)==raw);
 assert(signal==(raw&&!stale?demand:0));
 const auto end=policy(3,signal);
 assert(end.second==0);
 constexpr double outside=45*(9.0/2);
 const double gain=outside+demand*end.first;
 if(signal)assert(gain>=45*(37.0/8));else assert(gain==outside);
 return signal!=0;
}
int main(){
 int n=0,passed=0;
 for(int s:{-1,1})for(bool narrow:{false,true})for(bool stale:{false,true})
 for(bool erased:{false,true})for(int loadMode:{0,1,2}){
  passed+=record(s,narrow,stale,erased,loadMode);++n;
 }
 std::cout<<"earned cue cases "<<n<<"; qualified actuation "<<passed
          <<"; matched fallback "<<n-passed<<"\n";
}
