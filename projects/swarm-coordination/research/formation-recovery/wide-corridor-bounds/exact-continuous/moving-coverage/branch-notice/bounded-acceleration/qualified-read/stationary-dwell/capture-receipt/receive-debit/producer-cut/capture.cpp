#include "life_full.cpp"
#include "render_fixture.inc"
int main(){
  int far,w,how,cut;
  const std::string image="ignition.msgs.Image";
  while(std::cin>>far>>w>>how>>cut){
    NodeShared native;
    auto msg=[&](std::string pid,std::string id,std::string target){
      return MessagePublisher{depthTopic,pid,id,image,target,"fixture:"+pid};
    };
    auto old=msg("bridge-old","old","sensor");
    auto newp=msg("bridge-new","new","sensor");
    Node::Publisher::Data data{&native,msg("sensor","camera","sensor")};
    Node::Publisher pub{&data};
    native.OnNewRegistration(old);
    auto changing=[&](){
      switch(how){
        case 0:break;
        case 1:native.OnEndRegistration(old);break;
        case 2:expire(native,old.proc);break;
        case 3:bye(native,old.proc);break;
        case 4:native.OnNewRegistration(newp);native.OnEndRegistration(old);break;
        default:assert(false);
      }
    };
    if(cut==0)changing();
    RgbdCameraSensorPrivate d;
    d.depthNearClip=depthNear;d.depthFarClip=depthFar;d.pointPub.yes=true;
    Sensor s{&d};
    float target=far?37+w:7+w;
    const float p[]={5,1,2,0,target,3,4,0};
    Ogre2DepthCamera selected;
    selected.owned.newDepthFrame.fn=[&](const float* f,unsigned w,unsigned h,unsigned c,const std::string& k){
        d.OnNewDepthFrame(f,w,h,c,k);
    };
    selected.owned.newRgbPointCloud.fn=[&](const float* f,unsigned w,unsigned h,unsigned c,const std::string& k){
        d.OnNewRgbPointCloud(f,w,h,c,k);
    };
    selected.owned.texture.t.supplied=p;
    selected.PostRender();
    assert(d.depthBuffer[1]==target&&d.pointCloudBuffer[4]==target);
    // Authored additional producer-side read; it does not change any
    // consumed buffers. These are the raw, supplied synthetic samples.
    const float tapped=d.depthBuffer[1];
    const int tap=(tapped==(far?37:7))?0:(tapped==(far?38:8))?1:-1;
    d.depthPub.yes=pub.HasConnections();
    const bool atDepth=d.depthPub.yes;
    const int captureNanoseconds=far?477943485:425000000;
    s.emit(2,1,{0,captureNanoseconds});
    const bool imageEmitted=d.depthPub.images.size()==1;
    assert(imageEmitted==atDepth);
    if(imageEmitted){
      const auto& img=d.depthPub.images[0];
      assert(img.w==2&&img.h==1&&img.step==8&&img.hdr.t.nsec==captureNanoseconds);
      assert(img.hdr.values==std::vector<std::string>{"fixed-capture"}&&img.hdr.sequence==1);
      assert(img.pixels[0]==5&&img.pixels[1]==(far?float(math::INF_D):target));
    }
    if(cut==1)changing();
    const bool atPack=pub.HasConnections();
    s.mask(2);
    PointCloudUtil u;
    msgs::PointCloudPacked out{2};
    u.FillMsg(out,d.pointCloudBuffer,false,nullptr);
    assert(packed(out,0,0)==5);
    const float visible=packed(out,1,0);
    assert(visible==(far&&atDepth?float(math::INF_D):target));
    if(cut==2)changing();
    int stock=std::isfinite(visible)?(visible==(far?37:7)?0:1):-1;
    assert(tap==w);
    // A second physical sampling call on a different supplied viewpoint:
    // the native callback overwrites its raw buffer. The archived first bit
    // is unchanged; a latest-value producer read now answers a different view.
    const float follow[]={5,1,2,0,(far?37.0f:7.0f)+(1-w),3,4,0};
    selected.owned.texture.t.supplied=follow;
    selected.PostRender();
    int later=d.depthBuffer[1]==(far?37.0f:7.0f)?0:1;
    assert(later==1-w);
    std::cout<<atDepth<<' '<<atPack<<' '<<pub.HasConnections()<<' '
             <<imageEmitted<<' '<<stock<<' '<<tap<<' '<<later<<'\n';
  }
}
