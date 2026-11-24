"""Separately supplied providers, frozen consumer, and event-level observer."""
from itertools import combinations
from pathlib import Path
import importlib.util
import json

def module(path,name):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(path))
    mod=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

legacy=module('full.py','full_provider')
bank=module('bank.py','bank_provider')
consumer=module('consumer_reference.py','frozen_354')

def execute(n,r,B,name):
    source,ports = {
        'full': (legacy.publish, frozenset(range(n))),
        'bank': (bank.publish, frozenset(range(r+1))),
        'late': (bank.published_late, frozenset(range(r+1))),
    }[name]
    occupied,trace = consumer.setup(n, B)
    logs=[]
    def read(idx):
        assert idx in ports
        logs.append(idx)
        return idx not in occupied
    # Neither provider receives the reservation set, duty identities or
    # incumbent. Each can only ask the sensor port its declared lane reads.
    lane,delivery=source(n,r,read)
    assert set(logs)==ports and len(logs)==len(ports)
    assert lane in ports and lane not in occupied
    cert=(2,5,lane)
    producer_epoch=0 if name=='full' else 1
    current_epoch=producer_epoch
    # Waiting for the currently configured provider's receipt is an adapter
    # operation. The fixed consumer is unchanged. Pre-cut setup includes a
    # carried obsolete-epoch packet (one in each replacement) as a control.
    mailbox=[(delivery,producer_epoch,cert)]
    if name!='full':
        mailbox.append((2,0,(2,5,min(set(range(n))-set(B)))))
    accepted=[payload for t,epoch,payload in mailbox if t<=2 and epoch==current_epoch]
    assert len(accepted)<=1
    readout=accepted[0] if accepted else None
    chosen=consumer.incumbent(readout)
    if chosen is not None:
        trace.append([2,'dispatch',chosen])
        trace.append([4,'complete-new-service',chosen])
    standalone=[evt for evt in trace if evt[1] not in ('dispatch','complete-new-service')]
    standalone += [[delivery,'dispatch',lane],[delivery+2,'complete-new-service',lane]]
    releases=[[5,'old-complete-and-release',l,j] for j,l in occupied.items()]
    trace+=releases
    standalone+=releases
    assert all(x[1] != 'dispatch' or x[2] not in occupied for x in trace+standalone)
    joint=consumer.physical_oracle(n,trace,4)
    solo=consumer.physical_oracle(n,standalone,5)
    assert joint==(r,name!='late') and solo==(r,True)
    return {'joint':joint,'solo':solo,'reads':len(logs),'report_received_by_2':readout,
            'ignored_epoch_payloads':len([x for x in mailbox if x[1]!=current_epoch])}

def main():
    suites,cuts,runs=0,0,0
    examples={}
    for n in range(2,9):
        for r in range(1,n):
            suites+=1
            outputs=set()
            for B in combinations(range(n),r):
                cuts+=1
                for name in ('full','bank','late'):
                    q=execute(n,r,B,name)
                    runs+=1
                    if name=='bank':
                        outputs.add(q['report_received_by_2'][2])
                    if (n,r,B)==(4,1,(0,)): examples[name]=q
            assert len(outputs)==r+1
    print(json.dumps({'suites':suites,'same_reached_cuts':cuts,'module_comparisons':runs,
                      'joint_and_standalone_trace_checks':2*runs,'examples':examples},
                     indent=2,sort_keys=True))
if __name__=='__main__': main()
