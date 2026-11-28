#include <rmf_traffic/blockade/Moderator.hpp>
#include <rmf_traffic/blockade/Writer.hpp>
#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <numeric>
#include <vector>
using namespace rmf_traffic::blockade;
Writer::Checkpoint p(double x,double y){return {{x,y},"civil-inspection",true};}
Writer::Reservation route(double x,double y,double u,double v){return {{p(x,y),p(u,v)},.25};}

struct Bay {
 Moderator m;
 int n,holder=1;
 explicit Bay(const std::vector<int>& order): n(order.size()) {
  m.set(1,1,route(-4,0,4,0));
  m.ready(1,1,0);
  for(int j=0;j<n;j++) {
   const double phi=std::acos(-1.)*(j+1)/(n+1);
   const double x=4*std::cos(phi),y=4*std::sin(phi);
   m.set(j+2,1,route(-x,-y,x,y));
  }
  for(int a:order)m.ready(a,1,0);
  assert(active()==1);
 }
 int active() {
  int x=0;
  for(int a=1;a<=n+1;a++){
   const auto r=m.assignments().ranges().at(a);
   if(r.begin==0&&r.end==1){assert(!x);x=a;}
  }
  return x;
 }
 void withdraw(int id) {
  assert(holder && id!=holder);
  m.release(id,1,0);
  assert(active()==holder);
 }
 int qualified_clear() {
  if(holder)m.reached(holder,1,1);
  holder=active();
  return holder;
 }
};

int control(const std::vector<int>& order) {
 Bay a(order);
 a.withdraw(2);
 assert(a.qualified_clear()==3);
 a.withdraw(4);
 return a.qualified_clear();
}

int main(){
 unsigned upfront=0,adaptive=0;
 for(int n=2;n<=6;n++){
  std::vector<int> order(n);
  std::iota(order.begin(),order.end(),2);
  do{
   for(int mask=0;mask<(1<<n);mask++){
    Bay a(order);
    std::vector<int> remaining;
    for(int id:order)
     if(mask&(1<<(id-2)))a.withdraw(id);else remaining.push_back(id);
    for(int id:remaining)assert(a.qualified_clear()==id);
    assert(a.qualified_clear()==0);
    ++upfront;
   }
   for(int k=0;k<=2;k++)for(bool reset:{false,true}){
    Bay a(order);
    auto waiting=order;
    int remaining=k, previously=0;
    // These deletion decisions use only named waiters, the prior grant,
    // and the declared budget; the reference maintains its own queue.
    for(int h=0;h<n;h++){
     if(reset)remaining=k;
     if(remaining&&!waiting.empty()&&(h+previously)%3!=2){
      auto it=(previously%2==0?std::min_element(waiting.begin(),waiting.end()):
                              std::max_element(waiting.begin(),waiting.end()));
      a.withdraw(*it);waiting.erase(it);--remaining;
     }
     const int got=a.qualified_clear();
     assert(got==(waiting.empty()?0:waiting.front()));
     if(!got)break;
     previously=got;
     waiting.erase(waiting.begin());
    }
    ++adaptive;
   }
  }while(std::next_permutation(order.begin(),order.end()));
 }
 assert(control({2,3,4,5,6,7})==5);
 assert(control({2,3,4,6,5,7})==6);
 std::cout<<"upfront "<<upfront<<" adaptive "<<adaptive<<" renewed-control 5/6\n";
}
