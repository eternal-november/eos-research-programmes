#define main previous_native_fixture_main
#include "upstream_replay.cpp"
#undef main

struct Episode {
 World w{5};
 int open,failed,loc=0,t=-12,request_cut;
 bool request_erases, cue_erases, ack_erases;
 int request_seen=0,gate_seen=0,notice_seen=0,egress=-1,settled=-1,acks=0,other=0;
 int pending=-1,scout_receipt=0,commits=0;
 std::string ackBody="A1";
 int waitAck=0,ackAt=-1,rawAcks=0;
 bool reportErases=false;
 // Copies must be at the actual sending endpoint; a plan is not a copy.
 std::map<std::string,std::string> copies;
 static std::string bay(int j){assert(j==-1 || j==1);return j==1?"P":"Q";}
 void add(const std::string& who, double cap){
  auto node=std::make_shared<TeamNode>(*w.b.team->at("Base"));
  node->name=who; node->rf_state=rf_interface::radio_state{};
  node->radio.capacity=cap;
  w.b.team->emplace(who,node);w.b.endpoints[who+":7"]={{who}};
 }
 void dispatch(const std::string& s,const std::string& d,const std::string& p,int at,bool path=true){
  assert(t<=at);t=at;now=at*0.25;
  w.path_available=path;
  w.b.incomingMsgs.push_back({s,d,p});w.b.DispatchMessages();
  assert(w.b.incomingMsgs.empty());
 }
 Episode(int e,int f,int cut,bool request_erased,bool notice_erased,bool receipt_erased):
  open(e),failed(f),request_cut(cut),request_erases(request_erased),
  cue_erases(notice_erased),ack_erases(receipt_erased){
  for(auto a:{"Scout","Gate","Maint","Other","OBase"})add(a,80);
  // Two candidate relay copies were installed while joined, not assumed by address.
  w.b.endpoints["P:7"]={{"P"}};
  for(const std::string j:{"P","Q"})
   w.app.callbacks[j+":7"]=[&,j](auto s,auto,auto,auto v){if(s=="Scout"&&v=="R01")copies[j]=v;};
  w.app.callbacks["Gate:7"]=[&](auto s,auto,auto,auto v){if(s=="P"&&v=="G01")++request_seen;};
  w.app.callbacks["Scout:7"]=[&](auto s,auto,auto,auto v){
   if(s=="Maint"&&v=="M-L")notice_seen=-1;
   if(s=="Maint"&&v=="M-R")notice_seen=1;
   if(s=="Base"){++rawAcks;if(v=="A1"||v=="A01"){++acks;scout_receipt=1;ackAt=t;}}
  };
  w.app.callbacks["Base:7"]=[&](auto s,auto,auto,auto v){
   if((s=="P"||s=="Q")&&v=="R01")pending=t;
  };
  w.app.callbacks["OBase:7"]=[&](auto s,auto,auto,auto v){if(s=="Other"&&v=="U01")++other;};
  dispatch("Scout","P","R01",-11);dispatch("Scout","Q","R01",-6);
  assert(copies.at("P")=="R01"&&copies.at("Q")=="R01");
  dispatch("P","Gate","G01",request_cut,!request_erases);
  assert(request_seen==(!request_erases));
  assert(w.state("P").bytes_sent_this_epoch==3); // receiver failure does not undo sender debit.
 }
 // The sensor knows the state of the east gate only, via a modeled local test.
 // The retained layout law says precisely one guard leads out; paths to the
 // two guard faces continue to exist. Inspection never implies a delivery.
 int probe(){
  assert(loc==0);t=1;loc=1;
  if(!request_seen) return 0;
  gate_seen=(open==loc)?loc:-loc;
  return gate_seen;
 }
 void publish_loss(){
  // Authored loss-monitor adapter observes the one physical failed relay.
  // Scout only learns it when this separately dispatched typed cue arrives.
  assert(t==1);
  dispatch("Maint","Scout",failed==1?"M-R":"M-L",1,!cue_erases);
  dispatch("Other","OBase","U01",1,true); // unrelated route and receive footprint.
 }
 void move(int j){assert(j==-1||j==1);t+=std::abs(loc-j);loc=j;}
 void advance(int cut){assert(cut>=t);t=cut;}
 int attempt(){
  const auto sender=bay(loc);assert(copies.count(sender));
  const int cut=t; pending=-1;
  // Failure disables the radio effect, not the passage leading to its bay.
  dispatch(sender,"Base",copies.at(sender),cut,loc!=failed&&!reportErases);
  advance(cut+1);
  if(pending==cut){
   if(settled<0){settled=t;++commits;}
   if(waitAck>t)advance(waitAck);
   dispatch("Base","Scout",ackBody,t,!ack_erases);
  }
  // The policy sees callback evidence only. Silence need not mean no commit.
  return scout_receipt;
 }
 void leave(int exit){
  assert(exit==open);
  move(exit);advance(t+1);egress=t;
 }
 void carry(int exit){
  leave(exit);advance(t+4);
  // Authored exterior station: lawful named idempotent sink shares Base record.
  if(settled<0){settled=t;++commits;}
 }
 // Models a slower passive inspection at the east face when gate probe request
 // does not arrive. Never enters that face if closed.
 int mechanical_check(){assert(loc==1);advance(t+1);return open==1?1:-1;}
};

int main(){
 unsigned cases=0;
 for(int e:{-1,1})for(int f:{-1,1})for(int cut:{-1,0}) {
  Episode z(e,f,cut,false,false,false);
  const int route=z.probe();z.publish_loss();
  const int notice=z.notice_seen;
  assert(route==e && notice==f && z.other==1);
  z.move(-notice);
  if(z.loc==1) z.advance(std::max(z.t,cut+5));
  assert(z.attempt());
  z.leave(route);
  assert(z.commits==1 && z.acks==1 && z.settled>0);
  assert(z.settled==(f==1?4:cut+6));
  assert(z.egress==z.settled+(e==-f?1:3));
  assert((z.settled<=5&&z.egress<=8)==(cut==-1 || f==1));
  ++cases;
 }
 {
  // Same transport submission, no receipt and no old report received.
  Episode z(-1,-1,0,false,true,false);
  const int route=z.probe();z.publish_loss(); assert(!z.notice_seen);
  z.advance(4); assert(!z.attempt() && z.settled==-1);
  assert(z.w.state("P").bytes_sent_this_epoch==3);
  z.carry(route); assert(z.egress==8&&z.settled==12&&z.commits==1);
 }
 {
  // Same observed report timeout, but receiver committed and ACK was erased.
  Episode z(-1,-1,-1,false,true,true);
  const int route=z.probe();z.publish_loss();assert(!z.notice_seen);
  z.advance(4);assert(!z.attempt() && z.settled==5);
  z.carry(route);assert(z.egress==8&&z.settled==5&&z.commits==1);
 }
 {
  Episode z(1,-1,0,true,true,false);
  assert(!z.probe());
  z.publish_loss();assert(z.other==1);
  z.carry(z.mechanical_check());assert(z.egress==3&&z.settled==7);
 }
 {
  // Prior maintenance cue consumes Scout RX budget. Native RX evaluates the
  // present sender Base's limit, not Scout's larger advertised capacity.
  Episode full(-1,-1,-1,false,false,false);
  full.ackBody="A01";
  const int exit=full.probe();full.publish_loss();assert(full.notice_seen==-1);
  full.advance(4);assert(!full.attempt()&&full.settled==5&&full.rawAcks==0);
  assert(full.w.state("Base").bytes_sent_this_epoch==3);
  assert(full.w.state("Scout").bytes_received_this_epoch==3);

  Episode shortReply(-1,-1,-1,false,false,false);
  assert(shortReply.probe()==exit);shortReply.publish_loss();
  shortReply.advance(4);assert(shortReply.attempt()&&shortReply.ackAt==5);
  shortReply.leave(exit);assert(shortReply.egress==8&&shortReply.settled==5);
  assert(shortReply.w.state("Scout").bytes_received_this_epoch==5);

  Episode stale(-1,-1,-1,false,false,false);
  stale.ackBody="A0";
  assert(stale.probe()==exit);stale.publish_loss();stale.advance(4);
  assert(!stale.attempt()&&stale.rawAcks==1&&stale.settled==5);

  Episode delayed(-1,-1,-1,false,false,false);
  delayed.ackBody="A01";delayed.waitAck=6;
  assert(delayed.probe()==exit);delayed.publish_loss();delayed.advance(4);
  assert(delayed.attempt()&&delayed.ackAt==6&&delayed.settled==5);
  delayed.leave(exit);assert(delayed.egress==9);
  std::cout<<"confirmation: 3 bytes at 5 blocked; 2 bytes at 5 confirmed, egress 8;"
           <<" stale 2 bytes delivered but unqualified; 3 bytes at 6 confirmed, egress 9\n";
 }

 {
  // The scout did receive the maintenance cue in both histories. The
  // unsuccessful old route and the successful old route with a blocked
  // ACK have the same local silence, despite different actual service.
  Episode missing(-1,-1,-1,false,false,false);
  missing.ackBody="A01";missing.reportErases=true;
  const int route=missing.probe();missing.publish_loss();missing.advance(4);
  assert(missing.notice_seen==-1&&!missing.attempt()&&missing.rawAcks==0);
  assert(missing.settled<0);
  missing.carry(route);assert(missing.egress==8&&missing.settled==12);
  std::cout<<"qualified notice and local silence: safe carry fallback 8 / upload 12\n";
 }
 unsigned sweep=0;
 for(int e:{-1,1})for(int f:{-1,1})for(int cut:{-1,0})
 for(auto body:{"A1","A01","A0"})for(int wait:{0,6})
 for(bool lostReport:{false,true})for(bool lostAck:{false,true}){
  Episode z(e,f,cut,false,false,lostAck);
  z.ackBody=body;z.waitAck=wait;z.reportErases=lostReport;
  const int route=z.probe();z.publish_loss();const int which=z.notice_seen;
  assert(which!=0&&route!=0&&z.other==1);
  z.move(-which);
  if(z.loc==1)z.advance(std::max(z.t,cut+5));
  const bool matched=z.attempt();
  const int paid=f==1?4:cut+6;
  const int ack=std::max(paid,wait);
  const bool raw=!lostReport&&!lostAck&&std::string(body).size()+(ack<=5?3:0)<=5;
  assert(z.settled==(lostReport?-1:paid));
  assert((z.rawAcks==1)==raw);
  assert(matched==(raw&&std::string(body)!="A0"));
  if(matched){z.leave(route);assert(z.egress==ack+(e==-f?1:3));}
  else {z.carry(route);assert(z.commits==1);}
  ++sweep;
 }
 std::cout<<"matched native/direct scoped receipt histories "<<sweep<<"\n";
 std::cout<<"qualified native route and report cases "<<cases
          <<"; plus inclusive TX expiry, erased ACK, and gate-request erasure\n";
}
