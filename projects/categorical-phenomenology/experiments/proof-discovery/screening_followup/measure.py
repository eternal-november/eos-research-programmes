"""Post-outcome measurement extension; no algorithm or workload changes."""
import hashlib,json,statistics
from pathlib import Path
import followup as f
import experiment as e
P=Path(__file__).resolve().parent
Original=e.Cost
class Ledger(Original):
    latest=None; cpu_allowance=None
    def __init__(self,limit):
        super().__init__(limit,cpu_limit=self.cpu_allowance);self.overflow=0;Ledger.latest=self
    def add(self,part,n=1):
        try:return super().add(part,n)
        except e.OutOfBudget:
            if part=='kernel':self.overflow+=n
            raise

def summary(r):return {k:v for k,v in r.items() if k not in ('bundle','results','history')}
def one(mode,screen,cap,cpu_allowance=None):
    e.Cost=Ledger;Ledger.cpu_allowance=cpu_allowance
    try:r=f.run(mode,screen,cap);r['performed_uncharged_kernel_ticks']=Ledger.latest.overflow;r['cpu_allowance']=cpu_allowance
    finally:e.Cost=Original
    return r

def main():
    for line in (P.parent/'FINAL_SOURCE_SHA256.txt').read_text().splitlines():
        h,name=line.split();assert hashlib.sha256((P.parent/name).read_bytes()).hexdigest()==h,name
    for line in (P/'FROZEN_SHA256.txt').read_text().splitlines():
        h,name=line.split();assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h,name
    ledger=[]
    for cap in [100000,250000,1000000]:
        for screen in [343,8]:
            for mode in ['generic','guided']:
                ledger.append(summary(one(mode,screen,cap)))
    (P/'results'/'overflow_ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
    repeated=[]
    for rep in range(5):
        for screen in [343,8]:
            for mode in ['generic','guided']:
                r=one(mode,screen,10000000);r['repetition']=rep
                if rep==0:(P/'results'/f'{mode}_screen{screen}_complete.json').write_text(json.dumps(r,indent=2)+'\n')
                repeated.append(summary(r))
    (P/'results'/'timing_repeated.json').write_text(json.dumps(repeated,indent=2)+'\n')
    caps=[]
    for allowance in [0.5,0.8,1.5]:
        for rep in range(3):
            for screen in [343,8]:
                for mode in ['generic','guided']:
                    r=one(mode,screen,10**9,allowance);r['repetition']=rep;caps.append(summary(r))
    (P/'results'/'timing_capped.json').write_text(json.dumps(caps,indent=2)+'\n')
    for screen in [343,8]:
        for mode in ['generic','guided']:
            rs=[r for r in repeated if r['screen_size']==screen and r['mode']==mode]
            print(mode,screen,'all scored',[(r['positive_solved'],r['negative_rejected']) for r in rs],'proxy',rs[0]['cost']['total'],'cpu_median',statistics.median(r['cpu_seconds'] for r in rs))
if __name__=='__main__':main()
