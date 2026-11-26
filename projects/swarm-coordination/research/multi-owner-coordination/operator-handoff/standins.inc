#include <algorithm>
#include <cassert>
#include <deque>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <mutex>
#include <set>
#include <string>
#include <utility>
#include <vector>
struct Worker {
  std::deque<std::function<void(int)>> q;
  template<class F> void schedule(F cb){q.emplace_back(std::move(cb));}
  void drain(){while(!q.empty()){auto f=std::move(q.front());q.pop_front();f(0);}}
};
struct Context {
 Worker box;
 int clock=0;
 Worker& worker(){return box;}
 int now(){return ++clock;}
};
struct Task {
 std::string name;
 bool ready=false;
 int serial=0;
 std::set<std::string> holds;
 std::vector<std::function<void()>> ack;
 explicit Task(std::string v):name(std::move(v)){}
 const std::string& id()const{return name;}
 std::string add_interruption(const std::vector<std::string>&,int,std::function<void()> cb){
   auto token=std::to_string(++serial);
   holds.insert(token);ack.push_back(std::move(cb));
   return token;
 }
 bool is_interrupted() const{return ready&&!holds.empty();}
 void remove_interruption(std::initializer_list<std::string> ids,std::vector<std::string>,int){
   for(const auto& token:ids) assert(holds.erase(token)==1);
 }
 void internally_ready(){ready=true;for(const auto& cb:ack)cb();}
};
struct Slot {
 std::unique_ptr<Task> v;
 explicit operator bool()const{return bool(v);}
 Task* operator->()const{return v.get();}
 std::string id()const{return v->id();}
 std::string add_interruption(const std::vector<std::string>& l,int t,std::function<void()> f){return v->add_interruption(l,t,std::move(f));}
 void remove_interruption(std::initializer_list<std::string> a,std::vector<std::string> l,int t){v->remove_interruption(a,std::move(l),t);}
 bool is_interrupted()const{return v->is_interrupted();}
};
struct TaskManager : std::enable_shared_from_this<TaskManager> {
 struct Interruption {
   std::mutex mutex;
   bool resumed=false;
   std::weak_ptr<TaskManager> w_mgr;
   std::map<std::string,std::string> token_map;
   void resume(std::vector<std::string>);
   ~Interruption();
 };
 struct RobotInterrupt {
   std::weak_ptr<Interruption> interruption;
   std::vector<std::string> labels;
   std::function<void()> robot_is_interrupted;
 };
 Slot _active_task,_emergency_pullover,_waiting;
 std::shared_ptr<Context> _context=std::make_shared<Context>();
 std::vector<RobotInterrupt> _robot_interrupts;
 void interrupt_robot(std::shared_ptr<Interruption>,std::vector<std::string>,std::function<void()>);
 void _process_robot_interrupts();
 std::function<void()> _robot_interruption_callback();
};
