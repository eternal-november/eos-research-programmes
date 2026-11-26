#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "apriltag.h"
#include "tag36h11.h"

int main(void){
 apriltag_family_t *f=tag36h11_create();
 apriltag_detector_t *d=apriltag_detector_create();
 d->nthreads=1; d->quad_decimate=1;
 apriltag_detector_add_family_bits(d,f,0);
 int port,mode;
 while(scanf("%d %d",&port,&mode)==2){
   // Authored pixels, never a camera or localization guarantee.
   image_u8_t *im=image_u8_create(200,112);
   memset(im->buf,255,im->stride*im->height);
   if(mode!=1){
     int tag=(mode==2)?8:7;
     image_u8_t *stamp=apriltag_to_image(f,tag);
     int x0=port?120:30, y0=24;
     const int z=6;
     for(int y=0;y<stamp->height*z;++y)for(int x=0;x<stamp->width*z;++x)
       im->buf[(y0+y)*im->stride+x0+x]=stamp->buf[(y/z)*stamp->stride+x/z];
     image_u8_destroy(stamp);
   }
   zarray_t *res=apriltag_detector_detect(d,im);
   int n=zarray_size(res),code=-1,side=-1,bits=-1;
   if(n==1){
      apriltag_detection_t *p;
      zarray_get(res,0,&p);
      code=p->id; bits=p->hamming;
      side=p->c[0]>100.;
   }
   printf("%d %d %d %d\n",n,code,side,bits);
   apriltag_detections_destroy(res);image_u8_destroy(im);
 }
 apriltag_detector_destroy(d); tag36h11_destroy(f);
}
