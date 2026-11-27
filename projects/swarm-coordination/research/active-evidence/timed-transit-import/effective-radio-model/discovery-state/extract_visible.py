from pathlib import Path
from subprocess import check_output
P=Path
for line in P("VISIBILITY.tsv").read_text().splitlines():
    name,repo,ref,path,sha=line.split("\t")
    assert check_output(["git","hash-object",name],text=True).strip()==sha,name
def ext(f,start):
    s=P(f).read_text()
    begin=s.index(start)
    left=s.index("{",begin)
    i=left
    level=0
    for c in s[left:]:
        if c=="{":level+=1
        if c=="}":level-=1
        if level==0:return s[begin:i+1]+"\n"
        i+=1
    raise Exception(start)
p="table.cc"
v=ext(p,"VisibilityCost VisibilityTable::Cost(")
v+=ext(p,"void VisibilityTable::PopulateVisibilityInfo()")
v+=ext(p,"void VisibilityTable::PopulateVisibilityInfo(\n")
v+=ext(p,"bool VisibilityTable::PopulateVisibilityInfoHelper(")
v+=ext(p,"double VisibilityTable::MaxDistanceSingleHop(")
r="model.cc"
v+=ext(r,"rf_power VisibilityModel::ComputeReceivedPower(")
v+=ext(r,"void VisibilityModel::PopulateVisibilityInfo(")
v+="namespace range_model {\n"+ext("range.cc","rf_power log_normal_v2_received_power(")+"}\n"
P("visible.inc").write_text(v)
a=P("upstream_replay.cpp").read_text()
s=a.index("struct Vector3d {")
e=a.index("};",s)+2
vless=ext("Vector3.hh","public: bool operator<(const Vector3<T> &_pt) const")
vless=vless.replace("public: ","").replace("Vector3<T>","Vector3d")
a=a[:s]+'''struct Vector3d {
 double x=0,y=0,z=0;
 static const Vector3d Zero;
 double X()const{return x;} double Y()const{return y;} double Z()const{return z;}
 double Distance(const Vector3d& b)const{return std::hypot(x-b.x,y-b.y,z-b.z);}
 double operator[](int i) const { return i==0?x:i==1?y:z; }
 ORDER_OPERATOR
};
const Vector3d Vector3d::Zero{};'''.replace("ORDER_OPERATOR", vless.replace("this->data[","(*this)["))+a[e:]
s=a.index("struct Visibility {")
e=a.index("struct CommsBrokerPlugin",s)
a=a[:s]+'#include "visibility_shim.hpp"\n'+a[e:]
P("staged_replay.inc").write_text(a)
