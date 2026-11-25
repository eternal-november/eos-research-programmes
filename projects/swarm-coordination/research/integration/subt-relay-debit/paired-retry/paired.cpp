// Reuse the pinned development fixture; no networked or physical robot.
#define main original_subt_fixture_main
#include "upstream_replay.cpp"
#undef main
#include <array>
struct Result { bool early=false, late=false, debit=false; };

Result scenario(unsigned C,unsigned a,unsigned b,unsigned y,bool branch,bool early,bool late){
 World w(C);Ref direct{C,{},{}};
 auto other=std::make_shared<TeamNode>(*w.b.team->at("Q"));
 other->name="Other";w.b.team->emplace("Other",other);
 size_t named=0;
 w.app.callbacks["Base:7"]=[&](auto src,auto,auto,auto v){
   if(src=="P"&&v==std::string(y,'a'))++named;
   if(v.size())++w.recv;
 };
 auto call=[&](std::string src,unsigned size,double t,bool good,bool target){
   w.path_available=good;
   const size_t before=named;
   direct.send(src,"Base",size,t,good);
   bool stock=w.send(src,"Base",size,t);
   auto expected=!direct.rx["Base"].empty()
      && direct.rx["Base"].back()==std::make_pair(t,size);
   if(target)assert(stock==expected&&stock==(named!=before));
   assert(w.state(src).bytes_sent_this_epoch==Ref::valid(direct.tx[src],t));
   return stock;
 };
 if(!branch){call("Other",b,0,true,false);call("P",a,.25,false,false);}
 else {call("P",a,0,false,false);call("Other",b,.25,true,false);}
 assert(named==0);
 assert(Ref::valid(direct.tx["P"],1)==a&&Ref::valid(direct.rx["Base"],1)==b);
 w.recover();Result result;
 if(early){
   result.early=call("P",y,1.25,true,true);
   result.debit=(w.state("P").bytes_sent.back().first==1.25);
 }
 if(late)result.late=call("P",y,1.5,true,true);
 return result;
}

int main(){
 size_t para=0, worlds=0, separated=0;
 for(unsigned C=1;C<=10;++C)
  for(unsigned a=1;a<=C;++a)
   for(unsigned b=1;b<=C;++b)
    for(unsigned y=1;y<=C;++y){
     if(a+y<=C||b+y<=C)continue;
     for(bool branch:{false,true})
      for(bool early:{false,true})
       for(bool late:{false,true}){
         auto x=scenario(C,a,b,y,branch,early,late);
         assert(!x.early);
         assert(x.debit==(branch&&early));
         assert(x.late==(late&&(!early||!branch||2*y<=C)));
         ++worlds;
       }
     ++para; separated+=2*y>C;
    }
 for(bool branch:{false,true}){
   auto x=scenario(5,4,4,3,branch,true,true);
   assert(!x.early&&x.late==!branch);
 }
 std::cout<<"parameter_cases="<<para<<" source_worlds="<<worlds
  <<" shortest_two_send_splits="<<separated<<" exact_witness_cap5=true\n";
}
