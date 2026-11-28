from pathlib import Path
b=Path("temporal_parent.cpp").read_text()
assert b.count("int main(){")==1
Path("temporal_parent.inc").write_text(b.replace("int main(){","int inherited_scoped_test(){"))
