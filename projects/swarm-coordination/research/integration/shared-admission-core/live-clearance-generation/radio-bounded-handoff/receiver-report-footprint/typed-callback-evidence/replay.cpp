#include "scope.cpp"
#include "enqueue.inc"

static std::string rows(const std::deque<std::pair<double,uint64_t>> &q){
  std::ostringstream s;
  if(q.empty())return "-";
  for(size_t i=0;i<q.size();++i){
    if(i)s<<',';
    s<<q[i].first<<':'<<q[i].second;
  }
  return s.str();
}

static int ev=0;

static void tap(Broker &b){
  const auto prev=b.communication_function;
  b.communication_function=[&b,prev](const auto& radio,auto& tx,auto& rx,const auto &n){
    auto name=[&](auto& ref)->std::string {
      for(const auto& match:*b.team)
        if(&match.second->rf_state==&ref)return match.first;
      assert(false);
      return "";
    };
    const auto x=name(tx),y=name(rx);
    const auto a=rows(tx.bytes_sent),c=rows(rx.bytes_received);
    const auto e=prev(radio,tx,rx,n);
    std::cout<<"attempt "<<++ev<<' '<<tx.update_stamp<<' '<<x<<' '<<y<<' '<<n
             <<' '<<a<<' '<<c<<' '<<rows(tx.bytes_sent)<<' '<<rows(rx.bytes_received)
             <<' '<<std::get<0>(e)<<'\n';
    return e;
  };
}

static void tap_callbacks(CommsClient &app){
  for (auto &entry:app.callbacks) {
    const auto key=entry.first;const auto old=entry.second;
    entry.second=[=](auto src,auto dst,auto port,const auto &s){
      old(src,dst,port,s);
      std::cout<<"callback "<<++ev<<' '<<now<<' '<<src<<' '<<key<<' '<<s.size()<<' '<<s<<'\n';
    };
  }
}

#define main observed_reference_main
#include "observed.inc"
#undef main

int main(int argc,char** argv) {
  return observed_reference_main(argc,argv);
}
