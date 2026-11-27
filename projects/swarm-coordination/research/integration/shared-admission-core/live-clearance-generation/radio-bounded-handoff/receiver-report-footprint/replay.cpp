#include "scope.cpp"
#include "enqueue.inc"

struct Observation {
  unsigned ptx, pre, post, alt, qtx;
  int old, extra, read, preferred;
};

static Observation test(unsigned cap,unsigned pt,unsigned rx,int loc,int consume,
                        unsigned probe,const std::string &body,int arm) {
  Fixture f(cap);
  auto &b=f.w.b;
  auto bind=[&](const std::string &node, const std::string &key) {
    auto n=std::make_shared<TeamNode>();
    n->name=node; n->radio=b.team->at("P")->radio;
    assert(b.team->emplace(node,n).second);
    b.endpoints[key+":7"].push_back({node});
  };
  bind("Ingress","alt");bind("Verifier","ticket");
  bind("Reporter","rpt");bind("Fail","fail");
  if (loc==1) b.endpoints["sample:7"].push_back({"Base"});
  if (loc==2) b.endpoints["sample:7"].push_back({"Verifier"});
  int old=0,extra=0,read=0;
  f.w.app.callbacks["Base:7"]=[&](auto src,auto,auto,const auto& msg) {
    if (src=="P" && msg==body) {assert(!old);old=1;}
    else assert(src=="Reporter" && msg==std::string(rx,'b'));
  };
  f.w.app.callbacks["alt:7"]=[&](auto src,auto,auto,const auto& msg) {
    assert(src=="Q" && msg==body && !old);old=2;
  };
  f.w.app.callbacks["sample:7"]=[&](auto src,auto,auto,const auto& msg) {
    assert(src=="Reporter" && msg.size()==probe && !read);
    // Synthetic qualification context: the message carries a source
    // meter observation captured before its own send, not a future verdict.
    assert(msg[0]=='a' || msg[0]=='b');read=1+(msg[0]=='b');
  };
  f.w.app.callbacks["Far:7"]=[&](auto src,auto,auto,const auto& msg) {
    assert(src=="Q" && msg==std::string(160,'e') && !extra);extra=1;
  };
  auto sample=[&](double time){
    auto v=pins(900,40);
    v.push_back({"Ingress",{{100}}});v.push_back({"Reporter",{{100}}});
    v.push_back({"Verifier",{{100}}});v.push_back({"Fail",{{3000}}});
    f.frame(time,v);
  };
  sample(.25);
  if (pt) b.OnMessage({"P","fail",std::string(pt,'d')});
  if (rx) b.OnMessage({"Reporter","Base",std::string(rx,'b')});
  b.DispatchMessages();
  const auto pre=f.w.state("Base").bytes_received_this_epoch;
  const auto ptx=f.w.state("P").bytes_sent_this_epoch;
  assert(pre==rx && ptx==pt);
  const bool pre_ok=pre+body.size()+(arm==2 && consume?probe:0)<=cap;
  if (loc) {
    b.OnMessage({"Reporter","sample",std::string(probe,pre_ok?'b':'a')});
    b.DispatchMessages();
  }
  const auto post=f.w.state("Base").bytes_received_this_epoch;
  // One final dispatch; both senders already have authoritatively
  // provisioned copies. Release actions issue no querying side effect.
  bool p=false;
  if (arm==0) p=(ptx+body.size()<=cap && post+body.size()<=cap); // local read
  if (arm==1) p=(ptx+body.size()<=cap && read==2); // before-probe claim
  if (arm==2) p=(ptx+body.size()<=cap && read==2); // certified worst debit
  if (arm==3) p=false; // fixed backup
  sample(1.25);
  b.OnMessage({p?"P":"Q",p?"Base":"alt",body});
  b.OnMessage({"Q","Far",std::string(160,'e')});
  b.DispatchMessages();
  return {unsigned(ptx),unsigned(pre),unsigned(post),
          unsigned(f.w.state("Ingress").bytes_received_this_epoch),
          unsigned(f.w.state("Q").bytes_sent_this_epoch),old,extra,read,p};
}

int main(int argc,char**argv){
  assert(argc==2);
  std::string payload=argv[1];
  assert(payload.size()==173);
  unsigned cap,pt,rx,probe; int loc,consume,arm;
  while (std::cin>>cap>>pt>>rx>>loc>>consume>>probe>>arm) {
    const auto z=test(cap,pt,rx,loc,consume,probe,payload,arm);
    std::cout<<z.ptx<<' '<<z.pre<<' '<<z.post<<' '<<z.alt<<' '<<z.qtx<<' '
             <<z.old<<' '<<z.extra<<' '<<z.read<<' '<<z.preferred<<' '
             <<(z.old?payload:"-")<<'\n';
  }
}
