from pathlib import Path
s=Path("supported_source.cpp").read_text()
body=s[s.index("inline int card("):s.index("void otherWork(")]
Path("cover.inc").write_text(body)
s=Path("mission.baseline").read_text()
tag='#include <fstream>'
assert s.count(tag)==1
s=s.replace(tag,tag+'\n#include "cut_contract.h"')
tag='long long bound_leg('
assert s.count(tag)==1
s=s.replace(tag,'#include "cover.inc"\n\n'+tag)
tag=''' assert(argc==5);Scene s(argv[1]);'''
new=''' assert(argc==10);Scene s(argv[1]);
 const int policy=std::stoi(argv[5]);
 const unsigned aSupport=std::stoi(argv[6]), bSupport=std::stoi(argv[7]);
 const unsigned aMiss=std::stoi(argv[8]), bMiss=std::stoi(argv[9]);
 assert(policy>=0&&policy<=3 && aSupport>0&&bSupport>0&&(aSupport|bSupport)<=3);
 assert(!(aMiss&~aSupport)&&!(bMiss&~bSupport)&&card(aMiss)<=1&&card(bMiss)<=1);'''
assert s.count(tag)==1
s=s.replace(tag,new)
tag=''' auto aux1=r.route("R","Audit",one(0),secs(t));
 auto data1=r.route("R","D1",report,secs(t));'''
new=r''' const auto auxBase=t;
 // Preserve the actually reached rest stop. Cut times are exact binary
 // fractions and primary runs at the same cut for every comparison.
 const std::array<long long,2> auditCut{t+31250,t+62500};
 const std::array<std::string,2> added{"ObsEast","ObsWest"};
 auto live=[](const auto& xs,double at){
    unsigned n=0;for(const auto& v:xs)if(v.first>=at-1.)n+=v.second;return n;
 };
 auto fits=[&](long long at){
    const auto x=secs(at);
    return live(r.w.state("R").bytes_sent,x)+1<=cap &&
           live(r.w.state("Audit").bytes_received,x)+1<=cap;
 };
 unsigned w=0;
 for(unsigned i=0;i<2;++i) if(fits(auditCut[i]))w|=1<<i;
 assert(w==3);
 // Independently pin the native same-position link under the declared
 // deterministic source on these qualified support cuts. This isolated
 // proof witness does not spend any live controller credits.
 {
    Radio validation(s,cap);
    validation.where["R"]=r.where.at("R");
    for(auto at:auditCut)assert(validation.route("R","Audit",one(0),secs(at))==one(0));
 }
 const Cover envelope{w,{aSupport,bSupport,0},{1,1,0}};
 const unsigned active=policy==3?3:policy==0?activate(envelope,false,3):
        policy==1?activate(envelope,true,3):[&]{
           unsigned m=0;
           for(unsigned k=1;k<4;++k)
              if(direct(envelope,k)<card(w)&&card(k)>card(m))m=k;
           return m;
        }();
 assert(active!=0);
 for(unsigned i=0;i<2;++i)if(active&(1u<<i)){
    r.add(added[i],r.where.at(gate));
    const std::string byte(1,char('u'+i));
    assert(r.route(added[i],"Base",byte,secs(auxBase))==byte);
 }
 const auto normal_pose=r.w.b.pose_update_f;
 std::string aux1;
 unsigned used=0;
 for(unsigned i=0;i<2;++i){
    if(!aux1.empty())break;
    const bool deadA=(active&1)&&(aMiss&(1u<<i));
    const bool deadB=(active&2)&&(bMiss&(1u<<i));
    const auto qualified=cut::check({cut::Act::effect,true,true,fits(auditCut[i]),!deadA&&!deadB});
    if(qualified!=cut::enable)continue;
    // Readiness was established in the fixture's serialized current cut,
    // and the actual native callback agrees. No fabricated queue wake.
    r.w.b.pose_update_f=[&](auto name){
       if((deadA&&name==added[0])||(deadB&&name==added[1]))return std::make_tuple(false,Pose{},now);
       return normal_pose(name);
    };
    aux1=r.route("R","Audit",one(0),secs(auditCut[i]));
    r.w.b.pose_update_f=normal_pose;
    assert(aux1==one(0));used=1+i;
 }
 const unsigned coverActual=(active&1?aMiss:0u)|(active&2?bMiss:0u);
 assert(bool(w&~coverActual)==!aux1.empty());
 assert(live(r.w.state("R").bytes_sent,secs(auditCut[1]))+5<=cap);
 // Mission's primary report retains one full five-byte native attempt.
 // Deferred observers receive their own results at the later cut.
 t=auditCut[1];
 for(unsigned i=0;i<2;++i)if(!(active&(1u<<i))){
    r.add(added[i],r.where.at(gate));
    const std::string byte(1,char('u'+i));
    assert(r.route(added[i],"Base",byte,secs(t))==byte);
 }
 // No observer role is silently deferred if required. This fixture's
 // temporary membership can end only after its own output is received.
 for(const auto& name:added)assert(r.w.b.Unregister(name));
 std::cout<<"window "<<w<<" "<<active<<" "<<used<<" "<<auxBase<<std::endl;
 auto data1=r.route("R","D1",report,secs(t));'''
assert s.count(tag)==1
Path("mission.cpp").write_text(s.replace(tag,new))
b=Path("bridge.baseline").read_text()
x='''def trace(binary,sites,world,miss,mode,cap,phase,promote,gaterule,gatecut,phasebit,calib):'''
y='''def trace(binary,sites,world,miss,mode,cap,phase,promote,gaterule,gatecut,phasebit,calib,win):'''
assert b.count(x)==1
b=b.replace(x,y)
x='''str(cap)],
                   stdin=PIPE'''
y='''str(cap),*map(str,win)],
                   stdin=PIPE'''
assert b.count(x)==1
b=b.replace(x,y)
x='''            x,primary,cut=read("primary",3)'''
y='''            w,active,used,base=map(int,read("window",4))
            policy,s1,s2,a,b=win
            full=(s1==s2 and s1!=3)
            expected_active=3 if policy==3 else 1 if policy==0 else 3 if full else 1
            assert w==3 and active==expected_active
            ready=w&~((a if active&1 else 0)|(b if active&2 else 0))
            expected_used=next((j+1 for j in range(2) if (ready>>j)&1),0)
            assert used==expected_used
            x,primary,cut=read("primary",3)
            assert int(cut)==base+62500 and bool(used)==(x!="-")'''
assert b.count(x)==1
b=b.replace(x,y)
x='''primary_commit=primary_effect,primary_arrival=primary!="-",backup_arrival=backup!="-")'''
y='''primary_commit=primary_effect,primary_arrival=primary!="-",backup_arrival=backup!="-",
                    early=active.bit_count(),used=used)'''
assert b.count(x)==1
b=b.replace(x,y)
a=b.index("    summary={}",b.index("def main("))
limit=b.index('if __name__=="__main__":',a)
b=b[:a]+'''    summary={}
    for policy in range(4):
        runs=[]
        for pair,(s1,s2,miss1,miss2) in enumerate(((1,1,1,1),(1,2,1,2),(3,3,0,0))):
            part=[trace(binary,sites,w,miss,3,6,dc,'checked',"clearance",gc,0,"resource-scoped",
                     (policy,s1,s2,miss1,miss2))
                   for w,miss,dc,gc in product(range(2),range(3),("before","after"),("before","after"))]
            expected=(pair!=1 or policy!=3)
            assert all(r["ack"] and r["effects"]==1 and r["audit"]==([1,2] if expected else [2])
                       and r["timely_effect"] and r["egress"]<454000000 for r in part)
            runs.extend(part)
        summary[policy]=dict(n=len(runs),old_audits=sum(1 in r["audit"] for r in runs),
            stable_returns=sum(r["ack"] and r["effects"]==1 for r in runs),
            independent_early=sum(r["early"] for r in runs),max_egress_us=max(r["egress"] for r in runs))
    assert summary[1]==summary[2]
    assert summary[1]["independent_early"]-summary[0]["independent_early"]==24
    assert summary[3]["old_audits"]==48
    print(json.dumps(summary,sort_keys=True))
''' + b[limit:]
Path("bridge.py").write_text(b)
