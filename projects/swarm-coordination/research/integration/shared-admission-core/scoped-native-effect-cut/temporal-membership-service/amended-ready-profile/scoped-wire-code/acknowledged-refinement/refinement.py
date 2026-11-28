from pathlib import Path
s=Path("prior_code.cpp").read_text()
a=s.index('    auto service=[]')
b=s.index('    for(unsigned s=0;s<=W;++s){',a)
implementation=s[a:b].strip()
assert implementation.endswith('};')
s=s[:a]+s[b:]
s=s.replace("int main(){",'#include "service.inc"\nint inherited_wire_main(){')
Path("prior_code.inc").write_text(s)
Path("service.inc").write_text('static '+implementation+'\n')
