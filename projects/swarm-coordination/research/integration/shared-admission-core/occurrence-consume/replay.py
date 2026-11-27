from pathlib import Path
import json,subprocess,sys
from normalize_gaz import source
from rank_audit import main as audit_rank

root=Path(__file__).resolve().parent
def main(up):
    gau=source(up)
    raw=subprocess.run([sys.executable,'-B',root/'normalize_radio.py',up/'radio'],
                       capture_output=True,text=True,check=True)
    rad=json.loads(raw.stdout)
    acc={'warehouse':sum(x["eligibility"] is not None for x in rad),
         'gazebo':sum(x["qualified"] is not None for x in gau)}
    print(json.dumps(dict(selected_setter=gau,station=rad,accepted=acc,rank_audit=audit_rank()),
                     indent=None,sort_keys=True))
if __name__=='__main__':main(Path(sys.argv[1]).resolve())
