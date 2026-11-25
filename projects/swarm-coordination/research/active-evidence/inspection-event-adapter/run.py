#!/usr/bin/env python3
from mission import Fixture, synth, execute
import argparse,json

def main():
    p=argparse.ArgumentParser()
    p.add_argument("fixture")
    p.add_argument("--traces",action="store_true")
    a=p.parse_args()
    f=Fixture.load(a.fixture)
    policy=synth(f,extract=True)
    if not policy:
        print(json.dumps({"feasible":False,"scope":"declared finite source worlds"}))
        return
    outcomes=[]
    for i in range(len(f.worlds)):
        rows=execute(f,i,policy)
        arrival=next(z.tick for t,o,a,z in rows if z.loc==f.d["base"])
        last=rows[-1][-1]
        result={"scenario":i,"actual_delivery":dict(last.delivered),
                "seen_receipts":dict(last.receipts),"egress":arrival,
                "remaining_charge":last.charge}
        if a.traces:result["trace"]=[{"tick":t,"local_view":v,"action":a,
                                    "actual_effect":{"position":z.loc,
                                     "rpt_commits":dict(z.delivered)}} for t,v,a,z in rows]
        outcomes.append(result)
    print(json.dumps({"feasible":True,"effects":outcomes},sort_keys=True))

if __name__=="__main__":main()
