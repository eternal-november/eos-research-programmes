#include <rmf_traffic/blockade/Moderator.hpp>
#include <rmf_traffic/blockade/Writer.hpp>
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <numeric>
#include <iostream>
#include <string>
#include <vector>
using namespace rmf_traffic::blockade;
Writer::Checkpoint p(double x,double y){return {{x,y},"inspection-bay",true};}
Writer::Reservation route(double x,double y,double u,double v){return {{p(x,y),p(u,v)},.25};}
int end(const Moderator& m,int i){return int(m.assignments().ranges().at(i).end);}
int ready(const Moderator& m,int i){return m.statuses().at(i).last_ready.has_value();}
int deletion_queries(){
 int checks=0;
 for(int n=2;n<=5;n++){
  std::vector<int> q(n);
  std::iota(q.begin(),q.end(),2);
  do{
   for(int drop=0;drop<(1<<n);drop++){
    Moderator m;
    m.set(1,1,route(-4,0,4,0));
    m.ready(1,1,0);
    for(int j=0;j<n;j++){
     const double phi=std::acos(-1.)*(j+1)/(n+1);
     const double x=4*std::cos(phi),y=4*std::sin(phi);
     m.set(j+2,1,route(-x,-y,x,y));
    }
    for(int j:q)m.ready(j,1,0);
    for(int j:q)assert(end(m,j)==0);
    for(int j=0;j<n;j++)if(drop&(1<<j))m.release(j+2,1,0);
    m.reached(1,1,1);
    const auto first=std::find_if(q.begin(),q.end(),
      [&](int i){return !(drop&(1<<(i-2)));});
    for(int j:q)assert(end(m,j)==int(first!=q.end()&&j==*first));
    ++checks;
   }
  }while(std::next_permutation(q.begin(),q.end()));
 }
 return checks;
}
int main(){
 std::cerr << "deletion queries "<<deletion_queries()<<"\n";
 // Use only serial library transitions; accepted assignments do not
 // move contenders. Only the incumbent exit is modeled as a real reach.
 for(int arm:{0,1}){
  std::string s="ABCRWX";
  do{
   if(s.find('W')<s.find('A') || s.find('R')<s.find('A'))continue;
   Moderator m;
   m.set(1,1,route(-4,0,4,0));
   m.ready(1,1,0);
   m.set(2,1,route(0,-4,0,4));
   m.set(3,1,route(-4,-4,4,4));
   m.set(4,1,route(12,-4,12,4));
   assert(end(m,1)==1&&end(m,2)==0&&end(m,3)==0&&end(m,4)==0);
   bool a_intent=false;
   std::cout<<arm<<" "<<s;
   for(char e:s){
    bool forward=false;
    switch(e){
     case 'A':a_intent=true;m.ready(2,1,0);break;
     case 'B':m.ready(3,1,0);break;
     case 'C':m.reached(1,1,1);break;
     case 'W':a_intent=false;m.release(2,1,0);break;
     case 'R':forward=arm==0||a_intent;
              if(forward)m.ready(2,1,0);
              break;
     case 'X':m.ready(4,1,0);m.reached(4,1,1);break;
     default:assert(false);
    }
    std::cout<<" "<<ready(m,2)<<end(m,2)<<ready(m,3)<<end(m,3)
             <<end(m,4)<<m.statuses().at(1).last_reached<<int(a_intent)<<int(forward);
   }
   std::cout<<"\n";
  }while(std::next_permutation(s.begin(),s.end()));
 }
}
