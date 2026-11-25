from pathlib import Path
from hashlib import sha1
import subprocess
import tempfile

PIN={"controller_manager.cpp":"07d3fa768237875322ddea775386faceb46ebb50",
     "SwitchController.srv":"a9c8a28d065a7326049e7f2f4387b3ccac9537e7"}
def main():
    h=Path(__file__).resolve().parent
    for name,d in PIN.items():
        raw=(h/name).read_bytes()
        assert sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==d
    src=(h/'controller_manager.cpp').read_text()
    funcs=["controller_interface::return_type evaluate_switch_result("]+[
        "void ControllerManager::"+x+"(" for x in ("deactivate_controllers","switch_chained_mode","activate_controllers","manage_switch")]
    def extract(s):
        a=src.index(s)
        return src[a:src.index('\n}',a)+2]
    with tempfile.TemporaryDirectory() as d:
        p=Path(d)
        (p/'selected.inc').write_text('\n'.join(map(extract,funcs))+'\n')
        subprocess.run(["g++","-std=c++17","-O2","-pthread","-I",d,str(h/'harness.cpp'),"-o",str(p/'check')],check=True)
        subprocess.run([str(p/'check')],check=True)
if __name__=="__main__":
    main()
