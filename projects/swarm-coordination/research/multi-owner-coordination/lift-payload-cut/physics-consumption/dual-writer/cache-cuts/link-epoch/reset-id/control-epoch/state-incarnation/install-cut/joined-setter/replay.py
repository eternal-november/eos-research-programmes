#!/usr/bin/env python3
"""Run two pinned selected-body assemblies in one serial fixture process."""
from pathlib import Path
import re
import runpy
import subprocess
import sys
import tempfile
from unittest.mock import patch

ROOT=Path(__file__).resolve().parent
PINS=Path(sys.argv[1]).resolve()
real=subprocess.run

def assembled(script):
    captured=[]
    def intercept(args,**kw):
        if str(args[0])=="c++":
            src=[Path(p) for p in args if str(p).endswith(".cc")]
            assert len(src)==1
            captured.append(src[0].read_text())
            return
        if len(args)==1 and Path(args[0]).name=="probe":
            assert len(captured)==1
            return
        if str(args[0])==sys.executable and args[1]=="-B":
            with patch.object(sys,"argv",[str(x) for x in args[2:]]):
                runpy.run_path(str(args[2]),run_name="__main__")
            return
        return real(args,**kw)
    with patch.object(subprocess,"run",intercept),patch.object(sys,"argv",[str(script),str(PINS)]):
        runpy.run_path(str(script),run_name="__main__")
    assert len(captured)==1
    includes=re.findall(r"^#include[^\n]*",captured[0],flags=re.M)
    code=re.sub(r"^#include[^\n]*\n","",captured[0],flags=re.M)
    signature="int main(){return 0;}"
    assert code.count(signature)==1
    return includes,code.replace(signature,"")

def main():
    life,branch=assembled(ROOT/"lifecycle/replay.py"),assembled(ROOT/"actuation/dual-writer/cache-cuts/replay.py")
    includes=list(dict.fromkeys(life[0]+branch[0]))+["#include <array>"]
    code="\n".join(includes)+"\nnamespace graph {\n"+life[1]+"\n}\n#undef GZ_PROFILE\n"
    code+="namespace act {\n"+branch[1]+"\n}\n#undef GZ_PROFILE\n"
    code+=(ROOT/"joined.inc").read_text()
    with tempfile.TemporaryDirectory() as d:
        cc=Path(d)/"joined.cc"
        cc.write_text(code)
        bin=Path(d)/"joined"
        real(["c++","-std=c++20","-Wall","-Wextra","-Werror",cc,"-o",bin],check=True)
        real([bin],check=True)
if __name__=="__main__":main()
