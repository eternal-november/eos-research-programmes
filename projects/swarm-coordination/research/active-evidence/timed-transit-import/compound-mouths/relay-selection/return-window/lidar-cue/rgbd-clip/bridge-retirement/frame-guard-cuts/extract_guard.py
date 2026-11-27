from pathlib import Path as P
from hashlib import sha1

b=P("lifecycle.cpp").read_bytes()
assert sha1(f"blob {len(b)}\0".encode()+b).hexdigest()=="8fb7779bec0f5b3a836c99d4b9bbab1d04b71258"
s=b.decode()
assert s.count("int main(){")==1
P("lifecycle_selected.inc").write_text(s.replace("int main(){","int lifecycle_previous_main(){"))
