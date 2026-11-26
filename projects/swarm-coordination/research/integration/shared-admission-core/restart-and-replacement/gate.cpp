#define TIMED_SOURCE_LIBRARY
#include "driver.cpp"

// One station obligation is already known from durable intent. Here the
// measured application effect is accepting it in this simulated station.
// It is not receipt or proof of a physical cargo move.
int main(){
  int old,qfail,notice,gate,prep,policy,inline_run;
  while(std::cin>>old>>qfail>>notice>>gate>>prep>>policy>>inline_run){
    now=0;
    TimedSource t(.5);
    int effects=0, committed=-1, second=-1, third=-1, copies=0;
    unsigned side=0, boot=0, qsetup=0, csetup=0, read=0;
    bool station_record=false;
    bool supplier_record[3]={};
    bool cut_value=false, backup_order=false;
    auto dispatch=[&](const std::string& src,const std::string& app,int tick,int bits,bool drop){
      assert(now<=tick/8.);
      now=tick/8.;
      t.plant.path_available=!drop;
      t.plant.b.incomingMsgs.push_back({src,app,std::string(1,char(bits))});
      t.plant.b.DispatchMessages();
      assert(t.plant.b.incomingMsgs.empty());
      t.plant.path_available=true;
    };
    // A single consume-point transition represents an atomic station write
    // and completion record. When gate=0 records are supplier-private.
    auto bind=[&](std::string app,std::string phys,auto fun){
      t.plant.b.endpoints[app+":7"]={{phys}};
      t.plant.app.callbacks[app+":7"]=fun;
    };
    int supplier=0;
    for(auto name:{"oldUse","qUse","cUse"}){
      bind(name,"Base",[&,k=supplier++](auto,auto,auto,const auto& bytes){
        assert(bytes.size()==1 && bytes[0]==7);
        ++copies;
        auto& record=gate?station_record:supplier_record[k];
        if(!record){
          ++effects;
          if(effects==1)committed=int(now*8);
          if(effects==2)second=int(now*8);
          if(effects==3)third=int(now*8);
          record=true;
        }
      });
    }
    t.bind("IndependentWork","Far",side);
    t.bind("BootAck","P",boot);
    t.bind("qSetup","Q",qsetup);
    t.bind("cSetup","Second",csetup);
    bind("read","P",[&](auto,auto,auto,const auto& b){
      assert(b.size()==1);
      ++read;
      cut_value=bool(b[0]&1);
    });
    bind("swap","Second",[&](auto,auto,auto,const auto& b){
      assert(b.size()==1);
      backup_order=bool(b[0]&1);
    });
    if(old!=2) dispatch("P","oldUse",1,7,old==0);
    dispatch("Base","BootAck",1,0,true);
    // A typed separate reading of actual effect; no inference from the ACK.
    // Encoder includes the effect bit, not the old attempt's terminal status.
    if(notice==1)dispatch("Base","read",2,effects>0,false);
    int view=read?int(cut_value):-1;
    int child_keep=-1;
    if(inline_run){
      std::cout<<"restart "<<view<<' '<<boot<<std::endl;
      assert(bool(std::cin>>policy>>child_keep));
    }
    // policy: 0 wait; 1 blind retry; 2 observe then use (wait if absent);
    // 3 gated with a local supplier indication; 4 gated/timer hedge.
    bool keep=(policy==1 || policy>=3 || (policy==2 && view==0));
    if(inline_run){assert(int(keep)==child_keep);keep=child_keep;}
    if(keep)dispatch("P","qSetup",3,0,false);
    dispatch("Independent","IndependentWork",3,9,false);
    if(keep && prep)dispatch("P","cSetup",3,0,false);
    // After prep, Q's path can disappear before settlement. Its slot is spent.
    if(keep)dispatch("Q","qUse",4,7,qfail);
    if(keep && policy!=4)dispatch("Q","swap",5,qfail!=0,qfail==2);
    const bool backup=keep&&(policy==4||backup_order);
    if(backup && !prep)dispatch("P","cSetup",5,0,false);
    if(notice==2)dispatch("Base","read",5,effects>0,false); // past decision cut
    // Pending-old sensitivity: the old authorized effect was not actually
    // ruled out by a fresh negative read. Same gate (if present) sees it.
    if(old==2)dispatch("P","oldUse",6,7,false);
    if(backup)dispatch("Second","cUse",prep?6:8,7,false);
    uint64_t tx=0;
    for(auto name:{"P","Q","Base","Second","Independent"})
      tx+=t.plant.state(name).bytes_sent_this_epoch;
    std::cout<<view<<' '<<keep<<' '<<effects<<' '<<committed<<' '<<copies
             <<' '<<side<<' '<<boot<<' '<<qsetup<<' '<<csetup<<' '<<read<<' '<<tx<<' '<<second<<' '<<third<<' '<<backup_order<<std::endl;
  }
}
