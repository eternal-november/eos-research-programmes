import hashlib
from pathlib import Path
import sys

p=Path(sys.argv[1])/"resource_manager.cpp"
raw=p.read_bytes()
assert hashlib.sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()=="681a37cbf42349d776555e09efde30ca068c5186"
s=raw.decode()
def function(name,indent=""):
    a=s.index(name)
    b=s.index("\n"+indent+"}",a)
    return s[a:b+len(indent)+2]
group=function("return_type update_hardware_component_group_state(", "  ")
(Path(sys.argv[2])/"group.inc").write_text(group+"\n")
names=["return_type ResourceManager::set_component_state(",
       "bool ResourceManager::enforce_command_limits(",
       "HardwareReadWriteStatus ResourceManager::read(",
       "HardwareReadWriteStatus ResourceManager::write("]
(Path(sys.argv[2])/"manager.inc").write_text("\n\n".join(map(function,names))+"\n")
