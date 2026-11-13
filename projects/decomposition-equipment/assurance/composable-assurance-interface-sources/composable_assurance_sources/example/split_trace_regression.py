"""Supplemental executable split request trace; no acquisition or main-source change."""
import json,hashlib
from pathlib import Path
import numpy as np
from experiment import Interface,check,DependencyCache

def run():
    root=Path(__file__).parent;results=root/'results';main=json.loads((results/'results.json').read_text());rows=[]
    for case in main['family_runs']:
        interface=Interface(**json.loads((results/f"{case['id']}_interface.json").read_text()))
        n=len(interface.A);B=np.array(interface.B);remaining=set(range(n));cycles=[]
        while remaining:
            c=[];i=min(remaining)
            while i not in c:
                c.append(i);remaining.remove(i);i=int(np.flatnonzero(B[i])[0])
            cycles.append(c)
        arrivals={i:(-10 if k<3 else 0) for c in cycles for k,i in enumerate(c)}
        available={};trace=[];ends=[None]*n
        for i,arrival in sorted(arrivals.items(),key=lambda x:(x[1],x[0])):
            server=interface.fifo[i];start=max(arrival,available.get(server,arrival));finish=start+1
            available[server]=finish
            capture=arrival if interface.capture[i]=='request' else start
            ends[i]=capture//interface.clock_microticks
            trace.append({'channel':i,'arrival':arrival,'service_start':start,'delivery':finish,'capture_frame':ends[i]})
        expected={i:(-1 if k<3 else 0) for c in cycles for k,i in enumerate(c)}
        assert all(ends[i]==expected[i] for i in range(n))
        # Decision at end slot0, microtick10. Latest capture -10 or0 -> elapsed<=20 ticks.
        assert all(row['delivery']<=10 and 10-row['capture_frame']*10<=20 for row in trace)
        accepted,reason,bound=check(interface,ends,10,DependencyCache(n))
        original=next(o for o in case['outcomes'] if o['variant']=='split_windows')
        assert accepted==original['accepted'] and bound==original['operational_union_bound']
        tokens=interface.sources(ends)
        assert len(tokens)==3*len(set(interface.blocks))
        rows.append({'case':case['id'],'cycles_from_learned_B':cycles,'request_trace':trace,
          'decision_microtick':10,'endpoints':ends,'source_tokens':sorted(tokens),'token_count':len(tokens),
          'operational_union_bound':bound,'accepted':accepted,'reason':reason,
          'matches_original_split_case':True,'all_delivered_before_decision':True})
    out={'scope':'Supplemental trace validation only. Saved learned interfaces; no resampling or primary result changes.',
         'cases':rows,'passed':len(rows)}
    (results/'split_trace_regression.json').write_text(json.dumps(out,indent=2))
    tracked=['split_trace_regression.py','results/split_trace_regression.json']
    (root/'SUPPLEMENTAL_SPLIT_MANIFEST.json').write_text(json.dumps({f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in tracked},indent=2))
    print(f"Passed {len(rows)} actual split FIFO traces; all match original incidence/risk/rejection.")
if __name__=='__main__':run()
