#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
typedef int64_t tmv_t;
typedef int32_t Integer32;
typedef struct { unsigned char bytes[8]; } ID;

struct tsproc {
 tmv_t t1,t2,t3,t4;
 tmv_t filtered_delay;
 int mode,filtered_delay_valid;
 void* delay_filter;
 double clock_rate_ratio;
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
int64_t tmv_to_TimeInterval(tmv_t a) {return a;}
int cid_eq(const ID *a,const ID *b) {return memcmp(a,b,sizeof(*a))==0;}
void filter_reset(void *filter) {(void)filter;}
#define POW2_41 (2199023255552.0)
#define pr_debug(...) ((void)0)
#define pr_info(...) ((void)0)
enum servo_state { SERVO_UNLOCKED, SERVO_JUMP, SERVO_LOCKED, SERVO_LOCKED_STABLE };
enum notification {NOTIFY_TIME_SYNC,NOTIFY_PARENT_DATA_SET};
enum {MID_TIME_STATUS_NP=1,MID_PARENT_DATA_SET};
struct port {int unused;};
struct PortIdentity {int unused;};
struct clock {
 int step_window,step_window_counter,free_running;
 enum servo_state servo_state;
 tmv_t ingress_ts,master_offset,path_delay;
 struct tsproc *tsproc;
 double nrr;
 struct {
  Integer32 cumulativeScaledRateOffset,scaledLastGmPhaseChange;
  uint16_t gmTimeBaseIndicator;
  int64_t lastGmPhaseChange;
 } status;
 struct {struct {ID grandmasterIdentity;} pds;} dad;
 struct {ID clockIdentity;} dds;
 struct {int64_t offsetFromMaster;} cur;
 struct {int max_count;} stats;
 int clkid,write_phase_mode,utc_reject,io_fail;
 void *sanity_check;
 void *servo;
 struct port *uds_rw_port;
};
enum servo_state requested;
struct port actual_port;
enum servo_state clock_no_adjust(struct clock *c,tmv_t a,tmv_t b) {
 (void)c;(void)a;(void)b;return SERVO_UNLOCKED;
}
int clock_utc_correct(struct clock *c,tmv_t t){(void)t;return c->utc_reject;}
double servo_sample(void*s,int64_t z,int64_t t,double w,enum servo_state *out) {
 (void)s;(void)z;(void)t;(void)w;*out=requested;return 0;
}
double clock_rate_ratio(struct clock*c){return c->nrr;}
void tsproc_set_clock_rate_ratio(struct tsproc*t,double a){t->clock_rate_ratio=a;}
int operation_error;
int clockadj_set_freq(int x,double y){(void)x;(void)y;return operation_error;}
int clockadj_step(int x,int64_t y){(void)x;(void)y;return operation_error;}
int clockadj_set_phase(int x,int64_t y){(void)x;(void)y;return operation_error;}
void clockcheck_set_freq(void*x,double y){(void)x;(void)y;}
void clockcheck_step(void*x,int64_t y){(void)x;(void)y;}
int clock_synchronize_locked(struct clock*c,double adj){(void)adj;return c->io_fail;}
void clock_stats_update(void*x,double y,double z){(void)x;(void)y;(void)z;}
void servo_reset(void*x){(void)x;}
INSERT_DOWN
INSERT_UPDATE
INSERT_RESET
INSERT_STEPWINDOW

struct time_status_np {
 int64_t master_offset,ingress_time;
 Integer32 cumulativeScaledRateOffset,scaledLastGmPhaseChange;
 uint16_t gmTimeBaseIndicator;
 int64_t lastGmPhaseChange;
 Integer32 gmPresent;
 ID gmIdentity;
};
struct other { char data[sizeof(struct time_status_np)]; };
struct ptp_message {union { struct other bytes; struct time_status_np aligned; } data;};
void selected_copy(struct clock *c,struct time_status_np *out,int selector) {
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
struct ptp_message private_msg;
size_t sent=0;
struct time_status_np last;
int serialize_ok=1,listener=1;
struct PortIdentity port_identity(struct port *p){(void)p;return (struct PortIdentity){0};}
struct ptp_message *port_management_notify(struct PortIdentity p,struct port *u){
 (void)p;(void)u;return &private_msg;
}
int clock_management_fill_response(struct clock*c,void*a,void*b,struct ptp_message*m,int id) {
 (void)a;(void)b;
 selected_copy(c,&m->data.aligned,id);
 return 1;
}
int msg_pre_send(struct ptp_message *m){(void)m;return !serialize_ok;}
void clock_send_notification(struct clock*c,struct ptp_message*m,enum notification what) {
 (void)c;
 assert(what==NOTIFY_TIME_SYNC);
 if(listener){++sent;last=m->data.aligned;}
}
void msg_put(struct ptp_message*m){(void)m;}
INSERT_NOTIFY
INSERT_SYNC

void run(int valid,enum servo_state aim,int expect_sent,int64_t ingress,int64_t offset,
        int free_running,int utc_reject,int io_fail) {
 struct tsproc t={.filtered_delay=114,.mode=TSPROC_FILTER,.filtered_delay_valid=valid};
 struct clock c={.ingress_ts=100,.master_offset=2,.tsproc=&t,.nrr=1,
   .uds_rw_port=&actual_port,.free_running=free_running,
   .utc_reject=utc_reject,.io_fail=io_fail};
 requested=aim;
 sent=0;
 clock_synchronize(&c,1120,1000);
 struct time_status_np poll;
 selected_copy(&c,&poll,MID_TIME_STATUS_NP);
 assert(sent==(size_t)expect_sent && poll.ingress_time==ingress && poll.master_offset==offset);
 if(sent) assert(last.ingress_time==ingress&&last.master_offset==offset);
}
int main(void) {
 run(0,SERVO_LOCKED,0,1120,2,0,0,0);
 run(0,SERVO_UNLOCKED,0,1120,2,1,0,0);
 run(1,SERVO_LOCKED,1,1120,6,0,0,0);
 run(1,SERVO_UNLOCKED,1,1120,6,0,0,0);
 run(1,SERVO_UNLOCKED,1,1120,6,1,0,0);
 run(1,SERVO_JUMP,1,0,6,0,0,0);
 run(1,SERVO_LOCKED,0,1120,6,0,1,0);
 run(1,SERVO_LOCKED,0,1120,6,0,0,1);
 serialize_ok=0;
 run(1,SERVO_LOCKED,0,1120,6,0,0,0);
 serialize_ok=1;listener=0;
 run(1,SERVO_LOCKED,0,1120,6,0,0,0);
 puts("failed estimate: no sync notification; successful estimate may emit even while unlocked");
 puts("jump notification: computed value with ingress cleared to zero");
 puts("UTC, runtime, serialization, or listener controls can suppress observation");
}
