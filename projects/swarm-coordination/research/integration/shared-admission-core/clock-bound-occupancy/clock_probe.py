#!/usr/bin/env python3
"""Run pinned #503 code, emitting separate poll and notification facts."""
from hashlib import sha1
from pathlib import Path
import subprocess
import sys
import tempfile

ptp, fixture=map(Path,sys.argv[1:])
def pinned(path,blob):
    b=path.read_bytes()
    assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()==blob
    return b.decode()

c=pinned(ptp/'clock.c','7bacb099d56657691619ceb711ea7a07ed803085')
p=pinned(ptp/'tsproc.c','a871049602a40d1c02da0416de4f8e295df89508')
s=pinned(fixture/'fixture.c','abc9acb7c9ddbf610d3899be6b3f4a0093c71792')
def f(src,mark):
    i=src.index(mark)
    return src[i:src.index('\n}\n',i)+2]
for k,v in (
    ('INSERT_UPDATE',f(p,'int tsproc_update_offset(')),
    ('INSERT_DOWN',f(p,'void tsproc_down_ts(')),
    ('INSERT_RESET',f(p,'void tsproc_reset(')),
    ('INSERT_SYNC',f(c,'enum servo_state clock_synchronize(')),
    ('INSERT_NOTIFY',f(c,'void clock_notify_event(')),
    ('INSERT_STEPWINDOW',f(c,'static void clock_step_window(')),
    ('INSERT_TLV',c[c.index('\tcase MID_TIME_STATUS_NP:'):c.index('\tcase MID_GRANDMASTER_SETTINGS_NP:')])
):
    assert s.count(k)==1
    s=s.replace(k,v)
s=s[:s.index('int main(void)')]+r"""
int main(void) {
 for(int n=6;n<=9;n+=3)for(int fresh=0;fresh<=1;++fresh) {
    struct tsproc t={.filtered_delay=120-n,.mode=TSPROC_FILTER,.filtered_delay_valid=fresh};
    struct clock clk={.ingress_ts=100,.master_offset=n,.tsproc=&t,.nrr=1,
        .uds_rw_port=&actual_port};
    requested=SERVO_UNLOCKED;
    sent=0;
    clock_synchronize(&clk,1120,1000);
    struct time_status_np poll;
    selected_copy(&clk,&poll,MID_TIME_STATUS_NP);
    assert(poll.ingress_time==1120 && poll.master_offset==n);
    assert(sent==(size_t)fresh);
    if(sent) assert(last.ingress_time==poll.ingress_time&&last.master_offset==poll.master_offset);
    printf("%d %ld %ld %zu\n",n,(long)poll.ingress_time,(long)poll.master_offset,sent);
 }
}
"""
with tempfile.TemporaryDirectory() as tmp:
    x=Path(tmp)
    (x/'p.c').write_text(s)
    subprocess.run(['cc','-std=c11','-Wall','-Wextra','-o',str(x/'p'),str(x/'p.c')],check=True)
    subprocess.run([x/'p'],check=True)
