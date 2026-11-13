/* Synthetic timed assurance supervisor: integer-only decision path.
 * Public readouts are clearance packet, action ports and retained action history.
 * Future delay/brake outcome is never an input. Host tests do not certify WCET.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#define N 131072ULL
#define EPS_PPM 13247ULL /* outward rounding sqrt(46/(2*131072)) */
#ifndef ALPHA_PPM
#define ALPHA_PPM 100000ULL
#endif
static const int speeds[]={0,700,800,900,1000,1100,1200};
static const uint32_t counts[]={10333,22385,22530,10277,22531,10266,10306,22444};
typedef struct { uint8_t run[12]; uint8_t initialized; } Controller;
typedef struct { int64_t distance_um,error_um,reserve_um,timestamp_ms; int source; int rest_since_capture; } Packet;
static int clip(int x,int lo,int hi){ return x<lo?lo:(x>hi?hi:x); }
static int min_i(int x,int y){return x<y?x:y;}
static void commit_action(Controller *c,const int a[12]) {
 for(int i=0;i<12;i++) c->run[i]=a[i]==1?min_i(c->run[i]+1,4):0;
}
static int initialize_from_observed_history(Controller*c,const int past[4][12]) {
 memset(c,0,sizeof(*c));
 for(int t=0;t<4;t++){
  for(int i=0;i<12;i++)if(past[t][i]!=-1&&past[t][i]!=1)return 0;
  commit_action(c,past[t]);
 }
 c->initialized=1;return 1;
}
static int64_t stopping_um(int speed,int sensing,int network,int brake){
 int delay=min_i(100+10+sensing+network,310)+10; /* actuator/dispatch lag bound */
 int k=brake/100,n=(speed+k-1)/k;
 int64_t ramp=(int64_t)speed*speed/2;
 int64_t braking=5*((int64_t)(2*n-1)*speed-(int64_t)k*n*(n-1));
 return ramp+(int64_t)speed*delay+braking;
}
static int risk_accept(uint64_t bad,int unsafe_support){
 return !unsafe_support || (ALPHA_PPM>=EPS_PPM && bad*1000000ULL<=N*(ALPHA_PPM-EPS_PPM));
}
static int decide(const Controller*c,const int a[12],Packet p,int64_t now){
 if(now<0||now>1000000000000LL||p.timestamp_ms<0||p.timestamp_ms>1000000000000LL)return 0;
 if(!c->initialized||!p.rest_since_capture||p.source!=1||p.timestamp_ms>now||now-p.timestamp_ms>100||p.error_um<0||p.reserve_um<0||p.distance_um>1000000000LL||p.distance_um<0||p.error_um>1000000000LL||p.reserve_um>1000000000LL)return 0;
 for(int i=0;i<12;i++)if((a[i]!=-1&&a[i]!=1)||c->run[i]>4)return 0;
 int64_t clear=p.distance_um-p.error_um-p.reserve_um;if(clear<=0)return 0;
 int m[3];
 m[0]=2*a[7]+(2+a[7])*min_i(c->run[4],2)-2*min_i(c->run[8],4);
 m[1]=2*a[3]+(2+a[3])*min_i(c->run[6],3)-2*min_i(c->run[1],1);
 m[2]=2*a[5]+(2+a[5])*min_i(c->run[10],4)-2*min_i(c->run[4],2);
 int selected=0;
 for(int j=1;j<7;j++){
  uint64_t bad=0;int unsafe_support=0;
  for(int z=0;z<8;z++){
   int ys=m[0]+((z&1)?1:-1),yn=m[1]+((z&2)?1:-1),yb=m[2]+((z&4)?1:-1);
   int sensing=clip(150+50*ys,0,1000),network=clip(150+50*yn,0,1000),brake=clip(2500+500*yb,500,5000);
   if(stopping_um(speeds[j],sensing,network,brake)>=clear){bad+=counts[z];unsafe_support=1;}
  }
  if(risk_accept(bad,unsafe_support))selected=speeds[j];
 }
 return selected;
}
/* Local actuation executor. Brake is latched and has priority over all packets.
 * Clock and stage schedule are local; future sensor/network delays never enter.
 * ACK means a validated current-manoeuvre stop authorization at this tick.
 * The timeout becomes eligible at310ms after ramp; scheduling/physical
 * engagement adds at most10ms, hence mechanical engagement by320ms.
 */
typedef struct { int64_t start; int speed; unsigned sequence; int braking; int sample_requested; } Mission;
typedef struct { int target_speed; int brake; int request_sample; } DriveCommand;
static DriveCommand tick(Mission*m,int64_t now,int stop_ack,unsigned ack_sequence,int source){
 if(now<0||now>1000000000000LL||m->start<0||m->start>1000000000000LL){m->braking=1;DriveCommand fail={0,1,0};return fail;}
 int64_t elapsed=now-m->start;
 if(elapsed<0 || elapsed>=m->speed+310 || (stop_ack&&ack_sequence==m->sequence&&source==2))m->braking=1;
 DriveCommand out={0,m->braking,0};
 if(!m->braking){out.target_speed=min_i(m->speed,(int)elapsed);if(elapsed>=m->speed+100&&!m->sample_requested){out.request_sample=1;m->sample_requested=1;}}
 return out;
}
static void test_executor(void){
 assert(risk_accept(0,0));
 if(ALPHA_PPM<EPS_PPM)assert(!risk_accept(0,1)); /* unseen empirical cell is not absent support */

 int past[4][12],a[12];Controller initialized;
 for(int i=0;i<12;i++){a[i]=-1;for(int t=0;t<4;t++)past[t][i]=-1;}
 for(int t=1;t<4;t++)past[t][10]=1;
 assert(initialize_from_observed_history(&initialized,past));assert(initialized.run[10]==3);
 Packet packet={537000,0,0,0,1,1};assert(decide(&initialized,a,packet,0)==0);
 past[0][10]=1;assert(initialize_from_observed_history(&initialized,past));assert(initialized.run[10]==4);
 if(ALPHA_PPM==100000ULL)assert(decide(&initialized,a,packet,0)==700);

 for(int v=700;v<=1200;v+=100)for(int s=0;s<=100;s+=100)for(int n=0;n<=100;n+=100){
  Mission m={0,v,17,0,0};int first=-1;
  for(int time=0;time<=v+400;time+=10){
   int arrival=v+100+s+10+n;
   DriveCommand d=tick(&m,time,time==arrival,17,2);
   if(d.brake&&first<0)first=time;
   if(time>first&&first>=0)assert(d.brake);
  }
  assert(first==v+100+s+10+n);
 }
 Mission m={0,1000,9,0,0};
 assert(!tick(&m,100,1,8,2).brake); /* stale sequence */
 assert(!tick(&m,200,1,9,3).brake); /* wrong authority */
 assert(tick(&m,1310,0,0,0).brake); /* loss: local watchdog */
 assert(tick(&m,1400,0,0,0).brake); /* irreversible until separate reset */
 Mission jitter={0,1000,10,0,0};
 assert(!tick(&jitter,1095,0,0,0).request_sample);
 assert(tick(&jitter,1105,0,0,0).request_sample);
 assert(!tick(&jitter,1115,0,0,0).request_sample);
 assert(tick(&jitter,INT64_MAX,0,0,0).brake);
 Packet no_rest={1260000,0,0,0,1,0};assert(decide(&initialized,a,no_rest,0)==0);
}
/* Test harness only: serialized memory snapshots are not a sensor interface. */
int main(void){
 test_executor();
 Controller c;int a[12];long long distance;int age;
 while(scanf("%lld %d",&distance,&age)==2){
  memset(&c,0,sizeof(c));c.initialized=1;
  for(int i=0;i<12;i++)if(scanf("%d",&a[i])!=1)return 2;
  for(int i=0;i<12;i++){int r;if(scanf("%d",&r)!=1)return 2;c.run[i]=(uint8_t)r;}
  Packet p={distance,0,0,0,1,1};int chosen=decide(&c,a,p,age);
  commit_action(&c,a);
  printf("%d",chosen);for(int i=0;i<12;i++)printf(" %u",c.run[i]);printf("\n");
 }
 return 0;
}
