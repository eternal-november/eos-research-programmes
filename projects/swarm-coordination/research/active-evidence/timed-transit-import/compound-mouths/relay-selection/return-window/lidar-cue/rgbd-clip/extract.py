"""Extract the pinned RGB-D clip, point-mask and packet XYZ projection."""
from pathlib import Path as P
from hashlib import sha1
from xml.etree import ElementTree as XML
import re
for line in P("INPUTS.tsv").read_text().splitlines():
    local,repo,ref,remote,want=line.split("\t")
    data=P(local).read_bytes()
    assert sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==want
s=P("sensor.cc").read_text()
u=P("points.cc").read_text()
camera=XML.parse("model.sdf").find(".//sensor[@name='camera_front']/camera")
planes=[float(camera.findtext(p)) for p in ("clip/near","clip/far","depth_camera/clip/near","depth_camera/clip/far")]
assert planes==[.01,300,.1,10]
assert "SetFarClipPlane(cameraSdf->FarClip());" in s
assert "this->dataPtr->depthFarClip = cameraSdf->DepthFarClip();" in s
begin=s.index("bool RgbdCameraSensor::Update(")
render=s.index("this->Render();",begin)
sub=s.index("if (this->dataPtr->depthPub.HasConnections())",render)
sub_end=s.index("if (this->dataPtr->pointCloudBuffer)",sub)
point=s.index("if (this->dataPtr->pointPub.HasConnections())",sub_end)
loop0=s.index("if (this->dataPtr->hasDepthNearClip || this->dataPtr->hasDepthFarClip)",sub)
loop1=s.index("if ((this->dataPtr->hasDepthNearClip || this->dataPtr->hasDepthFarClip)",point)
assert sub < loop0 < sub_end < point < loop1 < s.index("this->dataPtr->pointsUtil.FillMsg(",point)
def take(a,b):
    start=a.index("{",b)
    d=1
    for i in range(start+1,len(a)):
        d+=(a[i]=="{")-(a[i]=="}")
        if d==0:return a[b:i+1]
    raise ValueError(b)
copy=take(s,s.index("void RgbdCameraSensorPrivate::OnNewDepthFrame("))
copy+= "\n"+take(s,s.index("void RgbdCameraSensorPrivate::OnNewRgbPointCloud("))
pack=take(u,u.index("void PointCloudUtil::FillMsg(msgs::PointCloudPacked &_msg,\n    const float *_pointCloudData"))
P("selected.inc").write_text("".join(f"constexpr double {n}={v};\n" for n,v in zip(("renderNear","renderFar","depthNear","depthFar"),planes))
    +copy+"\n"+pack+"\n"
    +"void Sensor::trim(unsigned depthSamples){\n"
    +s[sub:s.index("{",sub)+1]+"\n"+take(s,loop0)+"\n}\n}\n"
    +"void Sensor::mask(unsigned depthSamples){\n"
    +s[point:s.index("{",point)+1]+"\n"+take(s,loop1)+"\n}\n}\n")
