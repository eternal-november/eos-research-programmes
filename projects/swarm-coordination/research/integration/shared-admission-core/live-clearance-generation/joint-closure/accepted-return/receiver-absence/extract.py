from pathlib import Path
import subprocess,sys
def part(s,n):
    i=s.index(n)
    return s[i:s.index("\n}",s.index("\n{",i))+2]+"\n"
where=Path(__file__).parent
src=Path(sys.argv[1])
v=(src/"validator").read_text()
a=(src/"adapter").read_text()
m=(src/"manager").read_text()
lic=a[:a.index("*/")+2]
names=["void Adapter::Implementation::subscribe_orders(",
       "void Adapter::Implementation::publish_state(",
       "void Adapter::Implementation::request_state_publish(",
       "bool Adapter::Implementation::is_order_complete("]
pieces=[lic,(where/"fixture.hpp").read_text(),v[v.index("namespace vda5050_core::validation {"):],
        "namespace vda5050_core::client::adapter {",
        part(m,"void StateManager::set_order("),*(part(a,n) for n in names),"}",
        (where/"receiver.cc").read_text()]
out=Path(sys.argv[2])
out.with_suffix(".cc").write_text("\n".join(pieces))
subprocess.run(["c++","-std=c++20","-O2",str(out.with_suffix(".cc")),"-o",str(out)],check=True)
