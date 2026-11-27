#include "life_full.cpp"
#include "render_fixture.inc"
int main(){
  int code[2];
  const std::string image="ignition.msgs.Image";
  while(std::cin.read(reinterpret_cast<char*>(code),sizeof(code))){
    const bool far=code[0],retain=code[1];
    float pixels[8];
    assert(std::cin.read(reinterpret_cast<char*>(pixels),sizeof(pixels)));
    NodeShared native;
    auto msg=[&](const std::string& pid,const std::string& id){
      return MessagePublisher{depthTopic,pid,id,image,"sensor","fixture:"+pid};
    };
    Node::Publisher::Data data{&native,msg("sensor","camera")};
    Node::Publisher pub{&data};
    auto old=msg("bridge-kept","old");
    native.OnNewRegistration(old);
    if(!retain)native.OnEndRegistration(old);
    RgbdCameraSensorPrivate d;
    d.depthNearClip=depthNear;d.depthFarClip=depthFar;d.pointPub.yes=true;
    Sensor s{&d};
    Ogre2DepthCamera pv;
    pv.owned.newDepthFrame.fn=[&](const float* f,unsigned w,unsigned h,unsigned c,const std::string& k){
        d.OnNewDepthFrame(f,w,h,c,k);
    };
    pv.owned.newRgbPointCloud.fn=[&](const float* f,unsigned w,unsigned h,unsigned c,const std::string& k){
        d.OnNewRgbPointCloud(f,w,h,c,k);
    };
    pv.owned.texture.t.supplied=pixels;
    pv.PostRender();
    assert(d.depthBuffer[1]==pixels[4]&&std::abs(d.depthBuffer[0]-5)<.01);
    auto identify=[&](float v){
      if(!std::isfinite(v))return -1;
      int start=far?37:7;
      for(int j=0;j<2;++j)if(std::abs(v-(start+j))<.05)return j;
      return -1;
    };
    int p=identify(d.depthBuffer[1]);
    d.depthPub.yes=pub.HasConnections();
    assert(d.depthPub.yes==retain);
    s.emit(2,1,{0,far?477943485:425000000});
    assert(d.depthPub.images.size()==unsigned(retain));
    if(retain)assert(d.depthPub.images.front().pixels[0]==pixels[0]);
    s.mask(2);
    PointCloudUtil u;
    msgs::PointCloudPacked out{2};
    u.FillMsg(out,d.pointCloudBuffer,false,nullptr);
    assert(packed(out,0,0)==pixels[0]);
    const auto x=packed(out,1,0);
    int bottom=identify(x);
    assert(bottom==(retain&&far?-1:p));
    std::cout<<retain<<' '<<p<<' '<<bottom<<'\n';
  }
}
