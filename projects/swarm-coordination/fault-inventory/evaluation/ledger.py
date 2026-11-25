"""Deterministic pin, coverage and reporting-route checks, not a coverage claim."""
import json,hashlib,re
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PINS=(("Swarm_Coordination_Fault_Inventory.tex","8113b594abd763a2ea45c4b7ef359d6b2e18ed57","f"),
      ("Swarm_Fault_Inventory_Cleanroom.tex","d47de465564c9bcc149a0af31074965916d89e5d","entry"))
IDENTITY="4359a8a1484498b9c46d8e58a0112448a1fba06b"

def read():
    out=[]
    for name,sha,macro in PINS:
        source=(ROOT/"sources"/name) if (ROOT/"sources"/name).exists() else ROOT.parent/name
        content=source.read_bytes()
        assert hashlib.sha1(f"blob {len(content)}\0".encode()+content).hexdigest()==sha
        pairs=re.findall(r"^\\"+macro+r"\{([A-Z]\d\d)\}\{([^}]+)\}",content.decode(),re.M)
        assert len(dict(pairs))==len(pairs)
        out.append(dict(pairs))
    return out

def baseline(rows):
    groups={}
    for id,name in rows.items(): groups[id]=dict(title=name,
        roles={"F":"mechanism","E":"architecture-dependent","A":"assurance","P":"probe",
               "S":"obligation","I":"interaction"}[id[0]],
        architecture_status="open",
        why_open="No accepted integrated reference-architecture coverage is established by this ledger.",
        scoped_support=[])
    return groups

def main():
    origin,comparison=read()
    all_ids={**origin,**comparison}
    assert len(all_ids)==110
    reg=baseline(all_ids)
    mapset=set()
    for l in (ROOT/"crosswalk.tsv").read_text().splitlines():
        first,other,reason=l.split("\t")
        y=other.split(",")
        assert first in origin and first not in mapset and len(set(y))==len(y) and reason
        assert all(a in comparison for a in y)
        mapset.add(first)
        reg[first]["related"]=sorted(y)
        reg[first]["discriminator"]=reason
        for a in y:reg[a].setdefault("reverse_related",[]).append(first)
    assert mapset==set(origin)
    assert all("reverse_related" in reg[i] for i in comparison)
    studies=json.loads((ROOT/"studies.json").read_text())
    for title,meta in studies.items():
        assert set(meta["labels"])<=set(all_ids) and "limit" in meta and "witness" in meta
        for i in meta["labels"]:reg[i]["scoped_support"].append(title)
    # Metadata, a previous proof, or analogue cannot mark an obligation passed.
    count=sum(bool(x["scoped_support"]) for x in reg.values())
    print(f'{len(reg)} pinned labels, {len(origin)} forward mapping rows with explicit reverse links')
    print(f'{count} labels mention scoped studies; {len(reg)-count} have no candidate study listed')
    print('0 integrated coverage claims: every item still needs architecture-level disposition')
    (ROOT/"ledger.json").write_text(json.dumps(dict(revision=IDENTITY,inventory=reg,explorations=studies),indent=2,ensure_ascii=False)+"\n")
if __name__=="__main__":main()
