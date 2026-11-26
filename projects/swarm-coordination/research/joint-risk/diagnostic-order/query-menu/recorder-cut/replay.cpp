#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <string>
#include <tuple>
#include <vector>
using rcutils_time_point_value_t=long;
namespace rclcpp {
struct QoS {};
struct QOSMessageLostInfo {};
struct MessageInfo {
 struct Fields{long source_timestamp,received_timestamp;uint32_t publication_sequence_number;};
 Fields fields;
 const Fields& get_rmw_message_info()const{return fields;}
};
struct SerializedMessage {std::string payload;};
using Fn=std::function<void(std::shared_ptr<const SerializedMessage>,const MessageInfo&)>;
struct GenericSubscription {Fn callback;};
struct SubscriptionOptions {
 struct Events {std::function<void(const QOSMessageLostInfo&)> message_lost_callback;} event_callbacks;
};
}
struct Node{
 long stamp=0;
 struct When{long n;long nanoseconds()const{return n;}};
 When now()const{return {stamp};}
 std::shared_ptr<rclcpp::GenericSubscription> create_generic_subscription(
   const std::string&,const std::string&,const rclcpp::QoS&, rclcpp::Fn fn,
   const rclcpp::SubscriptionOptions&){
   return std::make_shared<rclcpp::GenericSubscription>(rclcpp::GenericSubscription{fn});
 }
};
struct Writer{
 using Row=std::tuple<std::string,std::string,long,long,uint32_t>;
 std::vector<Row> rows;
 // Selected writer-interface overload; writer and storage body not executed.
 void write(std::shared_ptr<const rclcpp::SerializedMessage> m,const std::string& top,
   const std::string&,long r,long s,uint32_t seq=0){rows.emplace_back(top,m->payload,r,s,seq);}
};
struct RecorderImpl{
 std::unique_ptr<Node> node=std::make_unique<Node>();
 std::unique_ptr<Writer> writer_=std::make_unique<Writer>();
 struct Record{bool use_sim_time=false;} record_options_;
 struct Pause{bool load()const{return false;}} paused_;
 struct Last {void update(const std::string&,long,long){}} last_seen_timestamps_;
 void on_messages_lost_in_transport(const std::string&,const rclcpp::QOSMessageLostInfo&){}
 void handle_pending_resume_request(const std::string&,long,long){}
 void handle_pending_bag_split_request(const std::string&,long,long){}
 std::shared_ptr<rclcpp::GenericSubscription> create_subscription(
  const std::string&,const std::string&,const rclcpp::QoS&);
};
#include "subscription.inc"

std::pair<std::vector<Writer::Row>,unsigned> world(bool sim,bool crossed,bool include_identity){
 RecorderImpl r;
 r.record_options_.use_sim_time=sim;r.node->stamp=1000;
 auto a=r.create_subscription("A","fixture",rclcpp::QoS{});
 auto b=r.create_subscription("B","fixture",rclcpp::QoS{});
 bool joint[2][2]={{false,false},{false,false}};
 auto callback=[&](auto sub,int site,int seq){
   int episode=(crossed&&site==1)?1-seq:seq;
   bool failed=seq==0;
   joint[episode][site]=failed;
   long publish=200+seq*100+site*50;
   assert(publish>episode*100); // plausible processing delay on either source assignment
   auto s=std::string(failed?"1":"0");
   if(include_identity)s+=":"+std::to_string(episode);
   sub->callback(std::make_shared<rclcpp::SerializedMessage>(rclcpp::SerializedMessage{s}),
      rclcpp::MessageInfo{{publish,publish+10,uint32_t(seq+1)}});
 };
 callback(a,0,0);callback(b,1,0);callback(a,0,1);callback(b,1,1);
 return {r.writer_->rows,unsigned(joint[0][0]||joint[0][1])+unsigned(joint[1][0]||joint[1][1])};
}
int main(){
 for(bool sim:{false,true}){
   auto [a,ra]=world(sim,false,false);
   auto [b,rb]=world(sim,true,false);
   assert(a==b && ra==1&&rb==2);
   auto [tag1,_1]=world(sim,false,true);
   auto [tag2,_2]=world(sim,true,true);
   assert(tag1!=tag2);
   std::cout<<(sim?"sim":"wall")<<" union_count "<<ra<<' '<<rb<<"\n";
   for(auto &[t,p,r,s,k]:a){
     assert(k==0);
     std::cout<<t<<' '<<p<<' '<<r<<' '<<s<<' '<<k<<'\n';
   }
 }
}
