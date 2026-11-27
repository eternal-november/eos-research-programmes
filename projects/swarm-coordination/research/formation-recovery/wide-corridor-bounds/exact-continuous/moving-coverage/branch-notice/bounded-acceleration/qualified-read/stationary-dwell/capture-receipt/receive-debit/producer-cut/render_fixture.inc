// The texture bus injects a CPU copy stand-in; no renderer geometry is produced.
enum PixelFormat {PF_FLOAT32_RGBA};
struct PixelUtil {
 static unsigned ChannelCount(PixelFormat f){assert(f==PF_FLOAT32_RGBA);return 4;}
};
namespace Ogre {
using PixelFormat=::PixelFormat;
struct PixelUtil{
 static size_t getMemorySize(unsigned w,unsigned h,unsigned d,PixelFormat f){
   return w*h*d*::PixelUtil::ChannelCount(f)*sizeof(float);
 }
};
struct PixelBox {
 unsigned width,height,depth;
 PixelFormat format;float* dst;
};
struct RenderTarget {
 enum {FB_AUTO};
 const float* supplied{};
 void copyContentsToMemory(PixelBox x,int){
   assert(supplied);
   std::memcpy(x.dst,supplied,PixelUtil::getMemorySize(x.width,x.height,x.depth,x.format));
 }
};
}
struct Ogre2Conversions {
 static Ogre::PixelFormat Convert(PixelFormat f){return f;}
};
struct Texture {
 Ogre::RenderTarget t;
 Texture* getBuffer(){return this;}
 Ogre::RenderTarget* getRenderTarget(){return &t;}
};
struct Event {
 std::function<void(const float*,unsigned,unsigned,unsigned,const std::string&)> fn;
 unsigned ConnectionCount()const{return fn?1:0;}
 void operator()(const float* p,unsigned w,unsigned h,unsigned c,const std::string& f){
   assert(fn);fn(p,w,h,c,f);
 }
};
struct Ogre2DepthCamera {
 struct Buffers {
   Texture texture;
   Texture* ogreDepthTexture=&texture;
   float *depthBuffer=nullptr,*depthImage=nullptr,*pointCloudImage=nullptr;
   Event newDepthFrame,newRgbPointCloud;
   ~Buffers(){delete[] depthBuffer;delete[] depthImage;delete[] pointCloudImage;}
 } owned;
 Buffers* dataPtr=&owned;
 unsigned ImageWidth()const{return 2;}
 unsigned ImageHeight()const{return 1;}
 void PostRender();
};
#include "render.inc"
