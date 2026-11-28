from pathlib import Path
import adapt_window

c=Path("clock_source.cpp").read_text()
r=c[c.index("using Pair="):c.index("struct Record")]
a='constexpr int first=4,last=6, earliest=3,deadline=9;'
b='constexpr int first=2,last=4, earliest=1,deadline=7;'
assert r.count(a)==1
Path("timer.inc").write_text(r.replace(a,b))
p=Path("mission.cpp")
s=p.read_text()
a=s.index(" assert(argc==10);")
b=s.index(" const int world",a)
s=s[:a]+''' assert(argc==9);Scene s(argv[1]);
 const int policy=std::stoi(argv[5]);
 const bool sameDriver=std::stoi(argv[6])!=0;
 const int offA=std::stoi(argv[7]), offB=std::stoi(argv[8]);
 assert(policy>=0&&policy<3);
 assert((offA==1||offA==-2)&&(offB==1||offB==-2));
 assert(!sameDriver||offA==offB);
'''+s[b:]
a='''#include "cover.inc"'''
b='''namespace Timed {
#include "timer.inc"
}'''
assert s.count(a)==1
s=s.replace(a,b)
a=s.index(' const auto auxBase=t;')
b=s.index(' auto data1=r.route(',a)
s=s[:a]+r''' const auto rest=t;
 const std::array<std::string,2> actors{"TimeA","TimeB"};
 struct Clock { int skew; int at(int q)const{return q+skew;} };
 auto aClock=std::make_shared<const Clock>(Clock{offA});
 auto bClock=sameDriver?aClock:std::make_shared<const Clock>(Clock{offB});
 const std::array<std::shared_ptr<const Clock>,2> commissioned{aClock,bClock};
 // The controlled commissioning evidence is identity of the actual
 // stable driving clock object. It does not disclose either offset.
 const bool provenCommon=commissioned[0]==commissioned[1];
 std::vector<Timed::History> support;
 for(int x:{1,-2})for(int y:{1,-2})
     if(x==y || !(policy==2||provenCommon))support.push_back({{0,0},{x,y}});
 auto possible=Timed::candidates(support);
 if(policy==1){
     std::vector<int> direct;
     for(int k=0;k<=Timed::deadline+1;++k)
         if(std::all_of(support.begin(),support.end(),[&](auto row){return Timed::ordinary(row,k);}))
             direct.push_back(k);
     assert(direct==possible);
 }
 assert(possible.empty()||(possible==std::vector<int>{3}));
 const int target=possible.empty()?-1:possible[0];
 const auto normal_pose=r.w.b.pose_update_f;
 for(auto name:actors)r.add(name,r.where.at(gate));
 r.add("Coordinator",0);
 std::array<int,2> localTarget{-1,-1},activated{-1,-1};
 if(target>=0)for(int i=0;i<2;++i){
     const auto msg=std::string(1,char(target));
     const auto got=r.route("Coordinator",actors[i],msg,secs(rest));
     assert(got==msg);
     localTarget[i]=int(got[0]);
 }
 r.w.b.Unregister("Coordinator");
 std::string aux1;
 for(int q=0;q<=Timed::deadline;++q){
     const long long at=rest+15625*q;
     for(int i=0;i<2;++i)
        if(localTarget[i]>=0&&activated[i]<0&&commissioned[i]->at(q)>=localTarget[i])
             activated[i]=q;
     if(q!=Timed::first&&q!=Timed::last)continue;
     const bool first=q==Timed::first;
     const bool deadA=first?activated[0]<0:activated[0]>=0;
     const bool deadB=first?activated[1]<0:activated[1]>=0;
     const auto x=secs(at);
     auto live=[](const auto& xs,double when){
        unsigned n=0;for(const auto& e:xs)if(e.first>=when-1.)n+=e.second;return n;
     };
     const auto finish=secs(rest+15625*Timed::deadline);
     const bool room=!aux1.empty() || (live(r.w.state("R").bytes_sent,x)+1<=cap &&
         live(r.w.state("Audit").bytes_received,x)+1<=cap &&
         live(r.w.state("R").bytes_sent,finish)+1+5<=cap);
     r.w.b.pose_update_f=[&](auto name){
        if((deadA&&name==actors[0])||(deadB&&name==actors[1]))return std::make_tuple(false,Pose{},now);
        return normal_pose(name);
     };
     now=x;
     bool ready=true;
     for(const auto& [name,node]:*r.w.b.team)ready&=std::get<0>(r.w.b.pose_update_f(node->name));
     assert(room&&ready==(!deadA&&!deadB));
     if(aux1.empty()&&cut::check({cut::Act::effect,true,true,room,ready})==cut::enable){
        aux1=r.route("R","Audit",one(0),x);
        assert(aux1==one(0));
     }
     r.w.b.pose_update_f=normal_pose;
 }
 for(const auto& a:actors)assert(r.w.b.Unregister(a));
 assert(target<0||((Timed::Pair{activated[0],activated[1]})==
        Timed::applied({{0,0},{offA,offB}},target)));
 assert(!aux1.empty()==(target<0||offA==offB));
 t=rest+Timed::deadline*15625;
 unsigned retainedTx=0;
 for(const auto& e:r.w.state("R").bytes_sent)if(e.first>=secs(t)-1.)retainedTx+=e.second;
 assert(retainedTx+5<=cap);
 std::cout<<"timer "<<target<<" "<<activated[0]<<" "<<activated[1]<<" "<<rest<<std::endl;
'''+s[b:]
p.write_text(s)
p=Path("bridge.py")
s=p.read_text()
a=s.index('            w,active,used,base=')
b=s.index('            assert max(b for _,a,b in rows)',a)
s=s[:a]+'''            target,actA,actB,rest=map(int,read("timer",4))
            policy,common,x,y=win
            want=3 if common or policy==2 else -1
            assert target==want
            if target<0:assert actA==actB==-1
            else:assert (actA,actB)==(target-x,target-y) and 1<=min(actA,actB)<=max(actA,actB)<=7
            x,primary,cut=read("primary",3)
            assert int(cut)==rest+7*15625
'''+s[b:]
s=s.replace('early=active.bit_count(),used=used)','activated=int(actA>=0 and actB>=0),target=target)')
a=s.index('    summary={}',s.index('def main'))
b=s.index('if __name__=="__main__":',a)
s=s[:a]+'''    summary={}
    for policy in range(3):
      names=("scope","direct","stale")
      records=[]
      for common,x,y in ((1,1,1),(1,-2,-2),(0,1,-2),(0,-2,1),(0,1,1),(0,-2,-2)):
         for w,gc,dc in product(range(2),("before","after"),("before","after")):
            r=trace(binary,sites,w,2,3,6,dc,'checked',"clearance",gc,0,"resource-scoped",
                     (policy,common,x,y))
            assert r["effects"]==1 and r["ack"] and r["egress"]<454000000 and r["timely_effect"]
            expected=x==y or policy!=2
            assert r["audit"]==([1,2] if expected else [2])
            records.append(r)
      summary[names[policy]]=dict(n=len(records),old=sum(1 in r["audit"] for r in records),
            actual_timers=sum(r["activated"] for r in records),egress=max(r["egress"] for r in records))
    assert summary["scope"]==summary["direct"]
    assert summary["scope"]["actual_timers"]==16 and summary["stale"]["old"]==32
    print(json.dumps(summary,sort_keys=True))
'''+s[b:]
p.write_text(s)
