#include "temporal_parent.inc"

struct Answer { bool old, bounded, delivered, moved; std::array<int,2> activations; };
Answer run(int bias,int shift,bool debt,int policy){
    Driver d; EffectCut x(d);
    std::array<std::string,2> actors={"ClockA","ClockB"};
    std::array<int,2> local{-1,-1}, offsets{bias,bias}, at{-1,-1};
    int witnessed=0;
    for(int i=0;i<2;++i){
        auto name=actors[i];
        assert(d.w.b.Register(name));d.w.b.endpoints[name+":7"]={{name}};
        d.w.app.callbacks[name+":7"]=[&,i](auto src,auto,auto,const auto& v){
            if(src=="P"){assert(i==1&&v=="prior");return;}
            if(src=="F"){assert(v==std::string(1,char(5))&&local[i]<0);local[i]=v[0];return;}
            assert(src=="Q"&&i==1&&v==std::string(1,char(shift+3)));
            witnessed=v[0]-3;
        };
    }
    auto send=[&](std::string s,int i,std::string p,double t){
        now=t;d.w.b.incomingMsgs.push_back({s,actors[i],p});
        d.w.b.DispatchMessages();assert(d.w.b.incomingMsgs.empty());
    };
    if(debt){send("P",1,"prior",0);assert(d.w.state(actors[1]).bytes_received_this_epoch==5);}
    for(int i=0;i<2;++i)send("F",i,std::string(1,char(5)),.125);
    assert(local[0]==5&&local[1]==5);
    send("Q",1,std::string(1,char(shift+3)),.25);
    assert((witnessed!=0)==!debt);
    assert(d.w.state("Q").bytes_sent_this_epoch==1);
    bool moved=false;
    if(policy==0&&witnessed){
        // The owner's decoder binds this exact relation to the proposed
        // coordinate generation. Rebase both read and trigger together.
        offsets[1]+=witnessed;local[1]+=witnessed;moved=true;
    }else if(policy==2){
        offsets[1]+=shift;moved=true;
    }
    // Policy 1 pins the previous physical clock at the action holder.
    d.durable[Radio::D]["diagnostic"]=diag;
    const auto prepared=x.prepare();
    bool old=false;
    for(int t=2;t<=10;++t){
       for(int i=0;i<2;++i)if(at[i]<0&&local[i]<=t+offsets[i])at[i]=t;
       if(t==4||t==6){
          x.lackingPose.clear();
          for(int i=0;i<2;++i)if(t==4?at[i]<0:at[i]>=0)x.lackingPose.insert(actors[i]);
          if(!old)old=x.commit(prepared,t*125000);
       }
    }
    const bool legal=std::all_of(at.begin(),at.end(),[](int t){return 3<=t&&t<=9;});
    return {old,legal,witnessed!=0,moved,at};
}
int main(){
    int verified=0,pinned=0,wrong=0,badAudit=0,badRange=0,anchoredMoves=0,kept=0;
    for(int bias:{1,-2})for(int shift:{2,-2})for(bool debt:{false,true}){
       auto good=run(bias,shift,debt,0), ordinary=run(bias,shift,debt,1),raw=run(bias,shift,debt,2);
       assert(good.activations==ordinary.activations&&good.old==ordinary.old&&good.bounded==ordinary.bounded);
       assert(good.old&&good.bounded && (good.moved==!debt)&&!ordinary.moved);
       assert(good.activations[0]==5-bias&&good.activations[1]==5-bias);
       assert(raw.activations[0]==5-bias&&raw.activations[1]==5-bias-shift);
       ++verified;++pinned;++wrong;
       anchoredMoves+=good.moved;kept+=!good.moved;
       badAudit+=!raw.old; badRange+=!raw.bounded;
    }
    assert(verified==8&&pinned==8&&wrong==8&&badAudit==4&&badRange==2&&anchoredMoves==4&&kept==4);
    std::cout<<"conditional translations "<<verified<<" ordinary physical pinning "<<pinned
      <<" true moves "<<anchoredMoves<<" blocked evidence retained source "<<kept
      <<" stale threshold old misses "<<badAudit<<" stale threshold early violations "<<badRange<<"\n";
}
