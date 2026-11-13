"""Randomized-block timing; frozen measurement order, unchanged algorithms."""
import hashlib,json,os,platform,random,statistics,sys,time
from pathlib import Path
from measure import one,summary
P=Path(__file__).resolve().parent

def main():
    for file,base in [(P.parent/'FINAL_SOURCE_SHA256.txt',P.parent),(P/'FROZEN_SHA256.txt',P)]:
        for line in file.read_text().splitlines():
            h,n=line.split();assert hashlib.sha256((base/n).read_bytes()).hexdigest()==h,n
    env={'python':sys.version,'platform':platform.platform(),'machine':platform.machine(),'processor':platform.processor(),'cpu_count':os.cpu_count(),'process_clock_resolution':time.get_clock_info('process_time').resolution,'performance_clock_resolution':time.get_clock_info('perf_counter').resolution}
    (P/'results'/'timing_environment.json').write_text(json.dumps(env,indent=2)+'\n')
    rng=random.Random(20261105);base=[(mode,screen) for screen in [343,8] for mode in ['generic','guided']]
    full=[];caps=[];order=[]
    for rep in range(5):
        block=list(base);rng.shuffle(block)
        for mode,screen in block:
            r=one(mode,screen,10000000);r['repetition']=rep;full.append(summary(r));order.append({'phase':'completion','repetition':rep,'mode':mode,'screen':screen})
    for allowance in [0.5,0.8,1.5]:
        for rep in range(3):
            block=list(base);rng.shuffle(block)
            for mode,screen in block:
                r=one(mode,screen,10**9,allowance);r['repetition']=rep;caps.append(summary(r));order.append({'phase':'cpu_cap','allowance':allowance,'repetition':rep,'mode':mode,'screen':screen})
    for name,obj in [('timing_randomized_complete.json',full),('timing_randomized_capped.json',caps),('timing_randomized_order.json',order)]:
        (P/'results'/name).write_text(json.dumps(obj,indent=2)+'\n')
    for mode,screen in base:
        rs=[r for r in full if r['mode']==mode and r['screen_size']==screen]
        print(mode,screen,'cpu_median',statistics.median(r['cpu_seconds'] for r in rs),'wall_median',statistics.median(r['wall_seconds'] for r in rs),'score',[(r['positive_solved'],r['negative_rejected'],r['status']) for r in rs],'proxy',rs[0]['cost']['total'])
if __name__=='__main__':main()
