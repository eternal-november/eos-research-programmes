#define main previous_fixture
#include "upstream_replay.cpp"
#undef main
#include <array>

using H=std::array<unsigned,4>;
bool checkNative(unsigned cap,H h,unsigned firstTime,unsigned first,
                 unsigned secondTime,unsigned second) {
  World w(cap);
  w.path_available=false;
  for(unsigned q=0;q<4;++q)
    if(h[q]) assert(!w.send("P","Base",h[q],double(q)/4));
  unsigned sum=0; for(auto n:h)sum+=n;
  assert(w.state("P").bytes_sent_this_epoch==sum);
  w.recover();
  auto other=std::make_shared<TeamNode>(*w.b.team->at("Base"));
  other->name="D2"; (*w.b.team)["D2"]=other;
  w.b.endpoints["D2:7"]={{"D2"}};
  w.app.callbacks["D2:7"]=[&](auto,auto,auto,auto s){ if(s.size()) ++w.recv; };
  bool a = !first || w.send("P","Base",first,1.0+double(firstTime)/4);
  bool b = !second || w.send("P","D2",second,1.0+double(secondTime)/4);
  return a && b;
}
unsigned p(H h,unsigned t){
  unsigned v=0;
  for(unsigned i=t;i<4;++i) v+=h[i];
  return v;
}
int main() {
 unsigned tested=0;
 for(unsigned cap=2;cap<=6;++cap)
 for(unsigned a=0;a<=cap;++a)
 for(unsigned b=0;a+b<=cap;++b)
 for(unsigned c=0;a+b+c<=cap;++c)
 for(unsigned d=0;a+b+c+d<=cap;++d) {
   H h{a,b,c,d};
   for(unsigned u=0;u<=5;++u)
   for(unsigned v=u;v<=5;++v)
   for(unsigned x=0;x<=cap;++x)
   for(unsigned y=0;y<=cap;++y){
     bool expected=p(h,u)+x<=cap && p(h,v)+y+(v-u<=4?x:0)<=cap;
     assert(checkNative(cap,h,u,x,v,y)==expected);
     ++tested;
   }
 }
 std::cout<<"pinned native two-probe suffixes "<<tested<<" across quarter ticks\n";
}
