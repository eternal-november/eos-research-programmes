#include <cassert>
#include <cmath>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <tuple>
#define RCLCPP_ERROR(...) ((void)0)

struct Point { double x=0,y=0; };
struct Pose { struct {Point position;} pose; struct {std::string frame_id;} header; };
struct TF {
 std::optional<Pose> reading;
 std::optional<Pose> getLatestPose(const std::string&,const std::string&,double,std::string*) {return reading;}
};
struct Node {int get_logger() const {return 0;}};
struct SimpleChargingDock {
 bool joint_state_sub_=false, is_stalled_=false, use_battery_status_=true, is_charging_=false;
 double transform_staleness_threshold_=0, docking_threshold_=0.05, charging_threshold_=0.5;
 Pose dock_pose_; std::string base_frame_id_="robot";
 std::shared_ptr<Node> node_=std::make_shared<Node>();
 std::shared_ptr<TF> tf_manager_=std::make_shared<TF>();
 bool isDocked(); bool isCharging(); bool disableCharging(); bool hasStoppedCharging();
 bool isCharger()const{return true;}
 void battery_sample(double);
};
struct Dock {int id; SimpleChargingDock* plugin;};
#include "source.inc"
#include "branches.inc"

struct Key {
 int goal, site, electrical, proxy, proximity, native_charge, mode;
 auto tuple() const {return std::tie(goal,site,electrical,proxy,proximity,native_charge,mode);}
 bool operator<(const Key& r)const{return tuple()<r.tuple();}
};
struct Count {size_t total=0, current=0;};
int main(){
 std::map<Key,Count> oracle;
 size_t observed=0, proxy_pass=0, proxy_false=0, verified=0, wrong_station=0,no_power=0;
 for(int goal:{0,1})for(int now:{-1,0,1})for(bool actual:{false,true}) {
  if(now<0&&actual)continue;
  for(int previous:{-1,0,1})for(int battery:{-1,0,1})
   for(bool freshTF:{false,true})for(bool useCurrent:{false,true})
    for(bool siteWitness:{false,true})for(bool currentWitness:{false,true}){
      SimpleChargingDock p; p.use_battery_status_=useCurrent;
      if(previous>=0){p.dock_pose_.pose.position.x=previous; p.dock_pose_.header.frame_id="dock_map";}
      if(freshTF){p.tf_manager_->reading=Pose{};p.tf_manager_->reading->pose.position.x=now;}
      if(battery>=0)p.battery_sample(battery);
      Dock A{0,&p},B{1,&p};
      const bool near=p.isDocked(),charge=p.isCharging();
      const bool pass=existing_dock_path(goal==0?&A:&B);
      assert(near==(freshTF&&now>=0&&now==previous));
      assert(charge==(useCurrent?battery==1:near));
      assert(pass==(near||charge) && existing_dock_path(&A)==existing_dock_path(&B));
      const bool truth=actual&&now==goal;
      Key k{goal,siteWitness?now:-2,currentWitness?int(actual):-1,int(pass),int(near),int(charge),int(useCurrent)};
      auto& bucket=oracle[k];bucket.total++;bucket.current+=truth;
      const bool admit=siteWitness&&now==goal&&currentWitness&&actual;
      assert(!admit||truth);
      observed++;proxy_pass+=pass;proxy_false+=pass&&!truth;verified+=admit;
      wrong_station+=pass&&actual&&now!=goal;
      no_power+=pass&&!actual;
    }
 }
 size_t forced=0, ambiguous=0, definite_no=0;
 for(auto&& [k,b]:oracle){
   const bool admit=k.site==k.goal && k.electrical==1;
   const bool strongest=b.current==b.total;
   assert(admit==strongest);
   forced+=strongest;ambiguous+=b.current>0&&b.current<b.total; definite_no+=b.current==0;
 }
 // Explicit witness: on a native proximity-only mode, the same stock result
 // remains true in either of these ordinary physical possibilities.
 SimpleChargingDock w;w.use_battery_status_=false;
 w.dock_pose_.header.frame_id="dock_map";w.tf_manager_->reading=Pose{};
 Dock D{0,&w};assert(existing_dock_path(&D)&&w.isDocked()&&w.isCharging());
 std::cout<<"scenarios="<<observed<<" stock_successes="<<proxy_pass
  <<" stock_not_named_current="<<proxy_false<<" already_powered_elsewhere="<<wrong_station
  <<" no_power="<<no_power<<" typed_admissions="<<verified
  <<" exact_all_world_keys="<<forced<<" ambiguous_keys="<<ambiguous
  <<" impossible_keys="<<definite_no<<"\n";
}
