"""Fixed negotiated representation for a keyed warehouse suffix.

Only query the log for a result after a receipt row has specified both
the operation payload and the committed tick. No log row creates a
receipt. The canonical full-archive digest remains unchanged.
"""
import json

def canonical(x):
    return json.dumps(x,sort_keys=True,separators=(",",":"))

def restore(value):
    if set(value)!={"base","log","receipts","permit"}:
        raise ValueError("unknown suffix schema")
    logs=value["log"]
    receipts=[]
    for row in value["receipts"]:
        if len(row)!=3:
            raise ValueError("wrong receipt shape")
        key,payload,tick=row
        if not isinstance(key,str) or not isinstance(payload,str) or type(tick) is not int:
            raise ValueError("untyped receipt index")
        matches=[res for at,act,res in logs if at==tick and act==payload]
        if len(matches)!=1 or not isinstance(matches[0],str):
            raise ValueError("missing or ambiguous receipt result")
        receipts.append([key,payload,tick,matches[0]])
    return {**value,"receipts":receipts}

def omit(value):
    trimmed={**value,"receipts":[r[:3] for r in value["receipts"]]}
    if restore(trimmed)!=value:
        raise ValueError("effect result not represented by log join")
    return trimmed

def mutated(value,kind):
    # Wire corruption controls are shaped so arrival cost stays the same.
    blob=json.loads(canonical(value))
    if kind=="wrong-key":blob["receipts"][0][0]="run:9"
    elif kind=="no-join":blob["receipts"][0][2]=9
    elif kind=="mutated-value":blob["log"][0][2]="[9,0]"
    else:raise ValueError("unknown fixture corruption")
    return blob

def codec_audit():
    def packet(cause):
        return dict(base="0"*64,log=[[8,"[0,4]",f"[{cause},0]"]],
                    receipts=[["run:7","[0,4]",8,f"[{cause},0]"]],
                    permit=[["run:7","[0,4]"]])
    def refuses(fn,candidate):
        try:fn(candidate)
        except ValueError:return
        raise AssertionError("expected refusal")
    verified=refused=0
    for i in range(5):
        for j in range(4):
            x=packet(i)
            if j==1:x["receipts"]=[]
            if j==2:x["receipts"][0][0]="alternate"
            if j==3:x["log"].append([9,"[0,4]","[0,0]"])
            assert restore(omit(x))==x
            verified+=1
        for k in range(4):
            x=packet(i)
            if k==0:x["log"]=[]
            if k==1:x["log"].append([8,"[0,4]",f"[{i},0]"])
            if k==2:x["receipts"][0][3]="[9,0]"
            if k==3:x["receipts"][0][1]="[0,9]"
            refuses(omit,x)
            refused+=1
        x=omit(packet(i))
        x["log"]=[]
        refuses(restore,x)
        refused+=1
    return dict(round_trips=verified,refusals=refused)
