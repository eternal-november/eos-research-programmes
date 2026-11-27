#include "life_color.cpp"
#include "render_fixture.inc"
int main(){
  int control[2];
  while(std::cin.read(reinterpret_cast<char*>(control),sizeof(control))){
    const bool point=control[0],keep=control[1];
    float pixels[8];
    assert(std::cin.read(reinterpret_cast<char*>(pixels),sizeof(pixels)));
    RgbdCameraSensorPrivate d;
    d.depthNearClip=depthNear;d.depthFarClip=depthFar;
    d.depthPub.yes=keep;d.pointPub.yes=point;d.imagePub.yes=true;
    Sensor s{&d};
    Ogre2DepthCamera r;
    r.owned.newDepthFrame.fn=[&](const float* f,unsigned w,unsigned h,unsigned c,const std::string& k){
        d.OnNewDepthFrame(f,w,h,c,k);
    };
    r.owned.newRgbPointCloud.fn=[&](const float* f,unsigned w,unsigned h,unsigned c,const std::string& k){
        d.OnNewRgbPointCloud(f,w,h,c,k);
    };
    r.owned.texture.t.supplied=pixels;r.PostRender();
    const ClockCut q{0,477943485};
    s.emit(2,1,q);
    assert(d.depthPub.images.size()==unsigned(keep));
    if(keep)assert(std::abs(d.depthPub.images.front().pixels[0]-5)<.01);
    msgs::PointCloudPacked out{2};
    if(point){
        s.mask(2);d.pointsUtil.FillMsg(out,d.pointCloudBuffer,true,d.image.Data<unsigned char>());
    }
    s.rgb(2,1,q,point);
    assert(d.imagePub.images.size()==1);
    auto& img=d.imagePub.images.front();
    assert(img.hdr.t.nsec==q.nsec&&img.step==6&&img.color.size()==6);
    auto color=[&](unsigned n)->int{return img.color[n];};
    auto label=(color(3)==127&&color(4)==31&&color(5)==15)?0:
               (color(3)==31&&color(4)==127&&color(5)==15)?1:-1;
    bool finite=false;
    if(point){
        finite=std::isfinite(packed(out,1,0));
        unsigned base=out.point_step()+12;
        assert(static_cast<unsigned char>(out.data[base])==color(5));
        assert(static_cast<unsigned char>(out.data[base+1])==color(4));
        assert(static_cast<unsigned char>(out.data[base+2])==color(3));
        assert(packed(out,0,0)==pixels[0]);
    }
    std::cout<<keep<<' '<<label<<' '<<point<<' '<<finite<<' '<<color(3)<<' '<<color(4)<<'\n';
  }
}
