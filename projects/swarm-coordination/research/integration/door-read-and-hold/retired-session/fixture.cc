#include <algorithm>
#include <cassert>
#include <iostream>
#include <map>
#include <optional>
#include <string>
#include <vector>

namespace builtin_interfaces::msg {struct Time {int sec=0;};}
using T=builtin_interfaces::msg::Time;
namespace rclcpp {
struct Time {
 int sec=0;
 Time()=default;
 Time(T t):sec(t.sec){}
 operator T()const{return {sec};}
 bool operator<(Time b)const{return sec<b.sec;}
};
}
namespace rmf_door_msgs::msg {
struct DoorMode {
 enum {MODE_OPEN=1,MODE_CLOSED,MODE_MOVING};
 int value=0;
};
struct DoorRequest {
 std::string door_name,requester_id;
 T request_time;
 DoorMode requested_mode;
};
struct Session {T request_time;std::string requester_id;};
struct DoorSessions {
 std::string door_name;
 std::vector<Session> sessions;
};
struct SupervisorHeartbeat {
 std::vector<DoorSessions> all_sessions;
};
}
using namespace rmf_door_msgs::msg;
const std::string DoorSupervisorRequesterID="supervisor";
template<class Message> struct Publisher {
 std::vector<Message> log;
 void publish(Message m){log.emplace_back(std::move(m));}
};
struct SimClock {T now()const{return {100};}};
struct Node {
 SimClock now;
 SimClock* get_clock(){return &now;}
 Publisher<DoorRequest> commands,*_door_request_pub=&commands;
 Publisher<SupervisorHeartbeat> heartbeats,*_door_heartbeat_pub=&heartbeats;
 std::map<std::string,std::map<std::string,rclcpp::Time>> _log;
 void _process_open_request(const std::string&,const std::string&,const T&);
 void _process_close_request(const std::string&,const std::string&,const T&);
 void _send_open_request(const std::string&);
 void _send_close_request(const std::string&);
 void _publish_heartbeat();
};
METHODS_SRC

void open(Node& n,std::string who,int t){n._process_open_request("gate",who,{t});}
void close(Node& n,std::string who,int t){n._process_close_request("gate",who,{t});}
std::optional<int> session(const Node& n,std::string who) {
 for(const auto& d:n.heartbeats.log.back().all_sessions)
  if(d.door_name=="gate")
   for(const auto& s:d.sessions)
    if(s.requester_id==who) return s.request_time.sec;
 return {};
}
struct Protected {
 Node n;
 std::map<std::string,int> closure;
 void open(std::string who,int t){
   auto p=closure.find(who);
   if(p!=closure.end() && t<=p->second) return;
   ::open(n,who,t);
 }
 void close(std::string who,int t){
   auto [i,new_entry]=closure.try_emplace(who,t);
   if(!new_entry)i->second=std::max(i->second,t);
   ::close(n,who,t);
 }
};

int main(){
 Node early,late;
 for(auto [n,term]:{std::pair{&early,12},std::pair{&late,15}}){
   open(*n,"crew",10);
   close(*n,"crew",term);
   assert(!session(*n,"crew"));
   assert(n->commands.log.back().requested_mode.value==DoorMode::MODE_CLOSED);
 }
 open(early,"crew",13);
 open(late,"crew",13);
 assert(session(early,"crew")==13 && session(late,"crew")==13);
 assert(early.commands.log.back().requested_mode.value==DoorMode::MODE_OPEN);
 assert(late.commands.log.back().requested_mode.value==DoorMode::MODE_OPEN);
 open(late,"crew",14);
 close(late,"crew",11);
 assert(session(late,"crew")==14);
 Node many;
 open(many,"crew",10);
 open(many,"other",10);
 size_t commands=many.commands.log.size();
 close(many,"crew",12);
 assert(many.commands.log.size()==commands);
 assert(!session(many,"crew")&&session(many,"other")==10);
 open(many,"crew",10);
 assert(session(many,"crew")==10);
 size_t after_replay=many.commands.log.size();
 close(many,"other",20);
 assert(many.commands.log.size()==after_replay && session(many,"crew")==10);
 Protected other_guard;
 other_guard.open("crew",10);
 other_guard.open("other",10);
 other_guard.close("crew",12);
 other_guard.open("crew",10);
 other_guard.close("other",20);
 assert(other_guard.n.commands.log.back().requested_mode.value==DoorMode::MODE_CLOSED);

 Protected good,bad;
 for(auto [n,term]:{std::pair{&good,12},std::pair{&bad,15}}){
   n->open("crew",10);
   n->close("crew",term);
 }
 good.open("crew",13);
 bad.open("crew",13);
 assert(session(good.n,"crew")==13 && !session(bad.n,"crew"));
 bad.open("crew",15);
 assert(!session(bad.n,"crew"));
 bad.open("crew",16);
 assert(session(bad.n,"crew")==16);
 bad.close("crew",14);
 assert(session(bad.n,"crew")==16);
 std::cout<<"different closures, same empty sessions; unqualified native open 13 accepted in both\n";
 std::cout<<"out-of-order close cannot erase a newer active open; another session prevents CLOSE\n";
 std::cout<<"late repeated open resurrects a retired session and blocks the other holder closing\n";
 std::cout<<"retired-time guard: 13 accepted after 12, not after 15; 16 accepted, exact tie denied\n";
}
