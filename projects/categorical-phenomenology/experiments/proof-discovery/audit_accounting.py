"""Independent ledger audit. Does not change the frozen experiment algorithm.

verify() computes a certificate check before requesting its cost charge. This
wrapper records a rejected kernel charge as performed-but-uncharged work.
Other charges are requested before their corresponding operation.
"""
import json
from pathlib import Path
import experiment as e
Original=e.Cost
class AuditedCost(Original):
    latest=None
    def __init__(self,*a,**kw):
        super().__init__(*a,**kw);self.rejected_kernel_ticks=0;AuditedCost.latest=self
    def add(self,part,n=1):
        try:super().add(part,n)
        except e.OutOfBudget:
            if part=='kernel':self.rejected_kernel_ticks+=n
            raise

def main():
    e.Cost=AuditedCost
    rows=[]
    for budget in [100000,1000000,10000000]:
        for method in ['definitions','training_cache','generic','guided','full_completion','guided_full_completion','cold','oracle']:
            r=e.run_method(method,budget);m=AuditedCost.latest
            rows.append({'budget':budget,'method':method,'status':r['status'],'charged_proxy':r['cost']['total'],'performed_uncharged_kernel_ticks':m.rejected_kernel_ticks,'proxy_including_overflow_verification':r['cost']['total']+m.rejected_kernel_ticks})
    p=Path(__file__).parent/'results'/'accounting_audit.json'
    p.write_text(json.dumps(rows,indent=2)+'\n')
    print('Deterministic runs:',len(rows),'with overflow verification:',sum(r['performed_uncharged_kernel_ticks']>0 for r in rows))
if __name__=='__main__':main()
