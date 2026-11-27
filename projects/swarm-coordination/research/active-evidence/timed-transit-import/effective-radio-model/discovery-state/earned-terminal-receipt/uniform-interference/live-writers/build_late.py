from hashlib import sha1
from pathlib import Path
p=Path(".")
parent=(p/"gate_budget.cpp").read_bytes()
sha=sha1(f"blob {len(parent)}\0".encode()+parent).hexdigest()
assert sha=="45f6d50c7110d8821ad754c09729bf6e02981bf1",sha
s=parent.decode()
s=s[:s.index('   const std::string key=')]

a=s.index(" const std::string requested=")
b=s.index(" size_t n;",a)
s=s[:a]+''' const std::string requested=argv[3], position=argv[4], guard=argv[5];
 assert(position=="prefix"||position=="gap"||position=="second"||position=="after");
 assert(guard=="none"||guard=="Q-snapshot"||guard=="Q-inline"||guard=="all-inline"||guard=="all-stale");
'''+s[b:]
(p/"late_writers.cpp").write_text(s+(p/"late_suffix.inc").read_text())
