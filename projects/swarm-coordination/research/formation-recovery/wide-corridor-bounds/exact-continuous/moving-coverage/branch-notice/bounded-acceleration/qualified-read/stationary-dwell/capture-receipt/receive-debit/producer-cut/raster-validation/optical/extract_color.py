"""Extract the original RGB output branch and color decode/copy methods."""
from pathlib import Path as P
base=P('sensor')
h=(base/'rgbd_full.cpp').read_text()
# Extend only the authored type fixture; observe exact original source below.
a=' void DecodeRGBAFromFloat(float, uint8_t&, uint8_t&, uint8_t&, uint8_t&)const {} // color not measured'
assert a in h
h=h.replace(a,''' void DecodeRGBAFromFloat(float, uint8_t&, uint8_t&, uint8_t&, uint8_t&)const;
 void RGBFromPointCloud(unsigned char*,const float*,unsigned,unsigned) const;''')
h=h.replace(' PixelFormatType pf{};std::vector<float> pixels;',
 ''' PixelFormatType pf{};std::vector<float> pixels;std::vector<unsigned char> color;
 void set_data(const unsigned char* data,unsigned bytes){color.assign(data,data+bytes);}''')
h=h.replace('enum class PixelFormatType {R_FLOAT32};','enum class PixelFormatType {R_FLOAT32,RGB_INT8};')
h=h.replace('enum Format {PF_FLOAT32_R};','''enum Format {PF_FLOAT32_R,PF_R8G8B8};
struct Image {
 std::vector<unsigned char> d = std::vector<unsigned char>(6);
 template<class T>T* Data(){return reinterpret_cast<T*>(d.data());}
};''')
h=h.replace('static unsigned BytesPerPixel(Format){return sizeof(float);}',
            'static unsigned BytesPerPixel(Format fmt){return fmt==PF_FLOAT32_R?sizeof(float):3;}')
h=h.replace(' Connected depthPub,pointPub;',
            ' Connected depthPub,pointPub,imagePub;\n rendering::Image image;PointCloudUtil pointsUtil;')
h=h.replace(' void emit(unsigned width,unsigned height,const ClockCut& _now);',
            ' void emit(unsigned width,unsigned height,const ClockCut& _now);\n void rgb(unsigned width,unsigned height,const ClockCut& _now,bool filledImgData);')
h=h.replace('assert(z=="depthImage");','assert(z=="depthImage"||z=="rgbdImage");')
h=h.replace('#include "publish.inc"','#include "publish.inc"\n#include "color.inc"')
(base/'rgbd_color.cpp').write_text(h)
life=(base/'life_full.cpp').read_text().split('int lifecycle_main(){',1)[0]
(base/'life_color.cpp').write_text(life.replace('rgbd_full.cpp','rgbd_color.cpp'))
s=(base/'sensor.cc').read_text();u=(base/'points.cc').read_text()
def take(text,token,end='\n}'):
  a=text.index(token);b=text.index(end,a)+len(end)
  return text[a:b]+'\n'
start=s.index('// publish the 2d image message',s.index('bool RgbdCameraSensor::Update('))
color=take(s[start:],'if (this->dataPtr->imagePub.HasConnections())','\n    }')
(base/'color.inc').write_text(take(u,'void PointCloudUtil::DecodeRGBAFromFloat(')
     +take(u,'void PointCloudUtil::RGBFromPointCloud(')
     +'void Sensor::rgb(unsigned width,unsigned height,const ClockCut& _now,bool filledImgData){\n'+color+'\n}\n')
