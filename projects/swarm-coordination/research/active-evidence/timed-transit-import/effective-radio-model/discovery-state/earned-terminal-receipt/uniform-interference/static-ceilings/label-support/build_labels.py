from hashlib import sha1
from pathlib import Path
s=Path("static_ceilings.cpp").read_bytes()
expected="0cc77f35b7f6f8e76682fa499164efb133df745a"
assert sha1(f"blob {len(s)}\0".encode()+s).hexdigest()==expected
s=s.decode()
s=s[:s.index('   const std::string key=')]
a=s.index(" assert(argc==")
z=s.index(" size_t n;",a)
s=s[:a]+''' assert(argc==5);
 const unsigned qcap=64,bcap=std::stoi(argv[1]);
 const auto requested=std::string("ba"),timeline=std::string(argv[2]),tags=std::string(argv[3]),mode=std::string(argv[4]);
 assert(mode=="fixed"||mode=="qualified"||mode=="clear"||mode=="keep"||mode=="blind");
 assert(tags.size()==5);
'''+s[z:]
s=s.replace("World w(32);","World w(64);")
Path('receipt_labels.cpp').write_text(s+Path('label_suffix.inc').read_text())
