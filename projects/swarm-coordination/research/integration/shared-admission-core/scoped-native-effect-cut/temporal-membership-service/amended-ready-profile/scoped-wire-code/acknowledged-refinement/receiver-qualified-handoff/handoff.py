from pathlib import Path
s=Path("refinement_source.cpp").read_text()
assert s.count("int main(){")==1
Path("handoff_parent.inc").write_text(s.replace("int main(){","int inherited_refinement_main(){"))
