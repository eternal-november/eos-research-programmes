"""Verify this deliberately open and pinned architecture docket, not I1."""
from copy import deepcopy
from hashlib import sha1
from pathlib import Path
import json
import re
import sys

here=Path(__file__).resolve().parent
def require(ok,label):
    if not ok:raise ValueError(label)

def blob(b):
    return sha1(f"blob {len(b)}\0".encode()+b).hexdigest()

def evaluate(m,data):
    require(m["format"]==1 and m["scope"]=="preflight-only","preflight scope")
    files=m["files"]|m["evidence"]
    require(set(files)==set(data),"input key set")
    for key,pin in files.items():
        require(re.fullmatch(r"[a-f0-9]{40}",pin["ref"]),"source commit")
        require(blob(data[key])==pin["blob"],"source blob")
    ids=[]
    for k,cmd in (("primary","f"),("cleanroom","entry")):
        ids+=re.findall(r"^\\"+cmd+r"\{([A-Z][0-9]{2})\}",
                        data[k].decode(),re.M)
    require(len(set(ids))==len(ids)==110,"inventory identifier set")
    crosswalk=json.loads(data["crosswalk"])
    require(crosswalk["revision"]==m["files"]["primary"]["ref"]
            ==m["files"]["cleanroom"]["ref"],"inventory revision")
    require(set(ids)==set(crosswalk["inventory"]),"crosswalk coverage")
    require(all(crosswalk["inventory"][i]["architecture_status"]=="open" for i in ids),
            "invented disposition")
    n=sum(bool(crosswalk["inventory"][i]["scoped_support"]) for i in ids)
    g=m["gates"]
    require(len({r["id"] for r in g})==len(g)==9,"gate count")
    for row in g:
        require(row["state"]=="open","invented closure")
        require(row["next"] and set(row["evidence"])<=set(m["evidence"]),"dangling evidence")
    return dict(pins=len(files),inventory=len(ids),scoped=n,open=len(ids),
           open_gates=len(g),ready_to_freeze=False,heldout_selected=False)

def main():
    m=json.loads((here/"manifest.json").read_text())
    home=Path(sys.argv[1])
    data={key:(home/key).read_bytes() for key in (m["files"]|m["evidence"])}
    out=evaluate(m,data)
    reject=0
    for bad in range(5):
        a,d=deepcopy(m),data.copy()
        if bad==0:d["640"]+=b"\n"
        elif bad==1:a["gates"][0]["state"]="accepted"
        elif bad==2:a["gates"][0]["evidence"].append("not-verified")
        elif bad==3:a["scope"]="acceptance"
        else:
            v=json.loads(d["crosswalk"])
            v["inventory"]["F01"]["architecture_status"]="tolerated"
            d["crosswalk"]=json.dumps(v).encode()
            a["files"]["crosswalk"]["blob"]=blob(d["crosswalk"])
        try:evaluate(a,d)
        except ValueError:reject+=1
    require(reject==5,"mutation checks")
    out["rejected_controls"]=reject
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=="__main__":main()
