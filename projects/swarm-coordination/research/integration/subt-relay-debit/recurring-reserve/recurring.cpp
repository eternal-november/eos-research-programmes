// Offline extension of the pinned development fixture. Local callbacks only.
#define main original_subt_fixture_main
#include "upstream_replay.cpp"
#undef main

struct Totals { unsigned reports=0, duties=0, copies=0, bad_debits=0; };
Totals run(unsigned cap,unsigned report,unsigned duty,unsigned old,size_t rounds,
          bool use_reserve,double duty_offset,bool primary_late_path=true){
 World w(cap); Ref direct{cap,{},{}};
 unsigned count_duty=0, actual_copies=0;
 const std::string packet(report,'a');
 w.b.endpoints["P:7"].push_back({"P"});
 w.app.callbacks["P:7"]=[&](auto src,auto,auto,const auto& v){
  if(src=="Q"&&v==std::string(duty,'a'))++count_duty;
 };
 w.app.callbacks["Q:7"]=[&](auto src,auto,auto,const auto& v){
   if(src=="P"&&v==packet){w.carried_copy=v;++actual_copies;}
 };
 w.recover();
 auto send=[&](std::string src,std::string dst,unsigned bytes,double at,bool good){
  w.path_available=good;
  auto old_base=w.recv, old_duty=(size_t)count_duty, old_copy=(size_t)actual_copies;
  auto [debit,arrive]=direct.send(src,dst,bytes,at,good);
  w.send(src,dst,bytes,at);
  assert(w.state(src).bytes_sent_this_epoch==Ref::valid(direct.tx[src],at));
  bool got=dst=="Base"?w.recv!=old_base:dst=="P"?count_duty!=old_duty:actual_copies!=old_copy;
  assert(got==arrive);
  if(got)assert(w.state(dst).bytes_received_this_epoch==Ref::valid(direct.rx[dst],at));
  return std::make_pair(debit,arrive);
 };
 Totals out;
 // Spacing is deliberately 3.75 s so each frame's two mandatory effects are
 // coupled by the rolling ledger, not by an unmodeled recharge at a boundary.
 for(size_t i=0;i<rounds;++i){
  const double t=i*3.75;
  w.carried_copy.clear();
  out.copies+=send("P","Q",report,t-1.5,true).second;
  // This models an old failed traffic obligation on P, not a fresh retry.
  assert(send("P","Base",old,t-.25,false).first);
  assert(w.carried_copy==packet); // backup sender must actually have the data
  if(use_reserve)
    out.reports+=send("Q","Base",report,t,true).second;
  auto independent=[&]{
   auto [debit,got]=send("Q","P",duty,t+duty_offset,true);
   out.duties+=got;out.bad_debits+=!got&&debit;
  };
  if(duty_offset<=1.0)independent();
  if(!use_reserve)
    out.reports+=send("P","Base",report,t+1.0,primary_late_path).second;
  if(duty_offset>1.0)independent();
 }
 return out;
}
int main(){
 unsigned checks=0;
 for(unsigned C=2;C<=9;++C)
  for(unsigned a=1;a<=C;++a)
   for(unsigned b=1;b<=C;++b)
    for(unsigned p=1;p<=C;++p)
      if(a+p>C)
       for(double delta:{.25,.5,.75,1.0}){
        constexpr unsigned N=12;
        const auto early=run(C,a,b,p,N,true,delta), late=run(C,a,b,p,N,false,delta);
        assert(early.reports==N && late.reports==N && late.duties==N);
        assert(early.duties == (a+b<=C?N:0));
        assert(early.copies==N&&late.copies==N&&early.bad_debits==0);
        checks+=2*N;
       }
 const auto early=run(5,3,4,4,40,true,0.5), late=run(5,3,4,4,40,false,0.5);
 const auto f_early=run(5,3,4,4,40,true,1.25,false),
            f_late=run(5,3,4,4,40,false,1.25,false);
 assert(f_early.reports==40&&f_early.duties==40&&f_late.reports==0&&f_late.duties==40);
 std::cout<<"matched native frame runs: "<<checks<<"\n";
 std::cout<<"early reserve: "<<early.reports<<" reports, "<<early.duties<<" distinct required replies\n";
 std::cout<<"wait for primary: "<<late.reports<<" reports, "<<late.duties<<" distinct required replies\n";
 std::cout<<"different fault branch: early reserve 40+40, waiting 0+40\n";
}
