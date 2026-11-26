#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
typedef int64_t tmv_t;
typedef int32_t Integer32;
typedef struct { unsigned char bytes[8]; } ID;
struct tsproc {
 tmv_t t1,t2,t3;
 tmv_t filtered_delay;
 int mode,filtered_delay_valid;
};
enum { TSPROC_FILTER, TSPROC_RAW, TSPROC_RAW_WEIGHT, TSPROC_FILTER_WEIGHT };
tmv_t tmv_zero(void) {return 0;}
int tmv_is_zero(tmv_t t) {return t==0;}
tmv_t tmv_sub(tmv_t a,tmv_t b) {return a-b;}
int tmv_sign(tmv_t x) {return (x>0)-(x<0);}
double tmv_dbl(tmv_t a) {return (double)a;}
tmv_t get_raw_delay(struct tsproc *t) {assert(0);return t->filtered_delay;}
int weighting(struct tsproc *t) {return t->mode==TSPROC_FILTER_WEIGHT;}
int64_t tmv_to_nanoseconds(tmv_t a) {return a;}
int cid_eq(const ID *a,const ID *b) {return memcmp(a,b,sizeof(*a))==0;}
#define POW2_41 (2199023255552.0)
#define pr_debug(...) ((void)0)
enum servo_state { SERVO_UNLOCKED, PREFIX_OK };
struct clock {
 int step_window,step_window_counter,free_running;
 enum servo_state servo_state;
 tmv_t ingress_ts,master_offset;
 struct tsproc *tsproc;
 double nrr;
 struct {
  Integer32 cumulativeScaledRateOffset,scaledLastGmPhaseChange;
  uint16_t gmTimeBaseIndicator;
  int64_t lastGmPhaseChange;
 } status;
 struct {struct {ID grandmasterIdentity;} pds;} dad;
 struct {ID clockIdentity;} dds;
};
enum servo_state clock_no_adjust(struct clock *c,tmv_t a,tmv_t b) {
 (void)c;(void)a;(void)b;assert(0);return SERVO_UNLOCKED;
}
INSERT_DOWN
INSERT_UPDATE
INSERT_PRE
 return PREFIX_OK;
}
struct time_status_np {
 int64_t master_offset,ingress_time;
 Integer32 cumulativeScaledRateOffset,scaledLastGmPhaseChange;
 uint16_t gmTimeBaseIndicator;
 int64_t lastGmPhaseChange;
 Integer32 gmPresent;
 ID gmIdentity;
};
struct other { char data[sizeof(struct time_status_np)]; };
enum { MID_TIME_STATUS_NP=1 };
void published(struct clock *c,struct time_status_np *out,int selector) {
 struct time_status_np *tsn;
 union { struct other bytes; struct time_status_np aligned; } buffer;
 memset(&buffer,0,sizeof(buffer));
 struct other *tlv=&buffer.bytes;
 size_t datalen=0;
 switch(selector){
INSERT_TLV
 }
 assert(datalen==sizeof(*out));
 memcpy(out,&buffer,datalen);
}
int main(void) {
 struct tsproc a={.filtered_delay=114,.mode=TSPROC_FILTER,.filtered_delay_valid=0};
 struct tsproc b=a;
 b.filtered_delay_valid=1;
 struct clock stale={.ingress_ts=100,.master_offset=6,.tsproc=&a,.nrr=1};
 struct clock fresh=stale;
 fresh.tsproc=&b;
 struct time_status_np older,first,second;
 published(&stale,&older,MID_TIME_STATUS_NP);
 assert(clock_synchronize(&stale,1120,1000)==SERVO_UNLOCKED);
 assert(clock_synchronize(&fresh,1120,1000)==PREFIX_OK);
 published(&stale,&first,MID_TIME_STATUS_NP);
 published(&fresh,&second,MID_TIME_STATUS_NP);
 assert(older.master_offset==6 && older.ingress_time==100);
 assert(first.master_offset==6 && first.ingress_time==1120);
 assert(memcmp(&first,&second,sizeof(first))==0);
 b.filtered_delay=113;
 assert(clock_synchronize(&fresh,1120,1000)==PREFIX_OK);
 published(&fresh,&second,MID_TIME_STATUS_NP);
 assert(second.master_offset==7 && second.ingress_time==1120);
 puts("missing valid delay: offset 6 retained, ingress changes from 100 to 1120");
 puts("fresh update: same report, but offset 6 recomputed; changed-delay control gives 7");
}
