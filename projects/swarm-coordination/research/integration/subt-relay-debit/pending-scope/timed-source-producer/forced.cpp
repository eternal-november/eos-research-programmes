#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

int main() {
  int stage,can_cancel,late,s,r;
  while(std::cin>>stage>>can_cancel>>late>>s>>r) {
    now=0;
    TimedSource v(late?1.25:.5);
    v.dispatch(v.preceding);
    v.dispatch({"Independent","Other",1,.125,false});
    assert(v.acquire(v.version));
    if(stage){ assert(!late);v.execute_new(stage==2); }
    bool first=v.amend(s,r);
    bool gone=false,second=first;
    if(!first && can_cancel){
      gone=v.cancel_optional();
      if(gone)second=v.amend(s,r);
    }
    if(v.reserved && v.fresh.when<v.tail.when)v.execute_new(false);
    const bool default_blocked=(v.tail.src=="Q"&&v.endpoint("OldTail")=="Second");
    // Authored physical unavailability of the original disjoint route.
    v.dispatch(v.tail,default_blocked);
    if(v.reserved)v.execute_new(false);
    assert(v.first==1&&v.independent==1);
    std::cout<<int(first)<<' '<<int(gone)<<' '<<int(second)<<' '
             <<v.first<<' '<<v.last<<' '<<v.optional<<' '<<v.independent<<' '
             <<int(default_blocked)<<'\n';
  }
}
