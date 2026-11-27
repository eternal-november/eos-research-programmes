"""Add the full pinned depth image block to the existing point fixture."""
from pathlib import Path as P
s=P('sensor.cc').read_text()
p=s.index('bool RgbdCameraSensor::Update(')
a=s.index('if (this->dataPtr->depthPub.HasConnections())',p)
b=s.index('  if (this->dataPtr->pointCloudBuffer)',a)
head=P('rgbd_probe.cpp').read_text()
shim=r'''
#define IGN_PROFILE(...) ((void)0)
namespace msgs {
enum class PixelFormatType {R_FLOAT32};
struct Time {
  int sec{},nsec{};
  void set_sec(int x){sec=x;}
  void set_nsec(int x){nsec=x;}
};
struct Header {
  Time t;std::string key;std::vector<std::string> values;unsigned sequence=0;
  Time* mutable_stamp(){return &t;}
  Header* add_data(){return this;}
  void set_key(std::string s){key=s;}
  void add_value(std::string s){values.push_back(s);}
};
struct Image {
 unsigned w{},h{},step{};Header hdr;
 PixelFormatType pf{};std::vector<float> pixels;
 void set_width(unsigned v){w=v;}
 void set_height(unsigned v){h=v;}
 void set_step(unsigned v){step=v;}
 void set_pixel_format_type(PixelFormatType p){pf=p;}
 Header* mutable_header(){return &hdr;}
 void set_data(const float* data,unsigned bytes){
   assert(bytes%sizeof(float)==0);
   pixels.assign(data,data+bytes/sizeof(float));
 }
};
}
namespace rendering {
enum Format {PF_FLOAT32_R};
struct PixelUtil {
 static unsigned BytesPerPixel(Format){return sizeof(float);}
 static unsigned MemorySize(Format f,unsigned w,unsigned h){return BytesPerPixel(f)*w*h;}
};
}
struct ClockCut {int sec,nsec;};
'''
head=head.replace('struct Connected {',shim+'\nstruct Connected {')
head=head.replace('bool HasConnections() const {return yes;}','''bool HasConnections() const {return yes;}
 std::vector<msgs::Image> images;
 void Publish(const msgs::Image& m){assert(yes);images.push_back(m);}''')
head=head.replace(' void trim(unsigned);',''' void trim(unsigned);
 void emit(unsigned width,unsigned height,const ClockCut& _now);
 const std::string FrameId() const {return "fixed-capture";}
 void AddSequence(msgs::Header* h,const std::string& z){assert(z=="depthImage");h->sequence=1;}''')
head=head.replace('#include "selected.inc"','#include "selected.inc"\n#include "publish.inc"')
P('rgbd_full.cpp').write_text(head)
P('publish.inc').write_text('void Sensor::emit(unsigned width,unsigned height,const ClockCut& _now){\n'
                         +'unsigned depthSamples=width*height;\n'+s[a:b]+'\n}\n')
# Retain the exact existing local native mask and retirement hooks, and
# rename their driver so the new scenario can link the unchanged helpers.
proj=P('lifecycle.cpp').read_text().replace('int main(){','int lifecycle_main(){')
P('life_full.cpp').write_text(proj.replace('rgbd_probe.cpp','rgbd_full.cpp'))

raw=P('render.cc').read_text()
i=raw.index('void Ogre2DepthCamera::PostRender()')
j=raw.index('\n}',i)+2
P('render.inc').write_text(raw[i:j]+'\n')
assert 'point.x > far - tolerance' in P('shader.glsl').read_text()
assert 'static_cast<float>(this->FarClipPlane())' in raw
assert 'EXPECT_FLOAT_EQ(scan[mid], mx);' in P('renderer-test.cc').read_text()
assert 'ign_find_package(ignition-rendering3 REQUIRED' in P('sensor-cmake.txt').read_text()
